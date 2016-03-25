(* Modified by TrustInSoft *)

(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2015                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

open Cil_types

let ploc_key = Structure.Key_Location.create_key "precise_locs"

module PLoc = struct

  type value = Cvalue.V.t
  type location = Precise_locs.precise_location
  type offset =
    | Precise of Precise_locs.precise_offset
    | Imprecise of Cvalue.V.t

  let structure = Structure.Key_Location.Leaf ploc_key

  let sizeof_lval_typ typlv =
    match Cil.unrollType typlv with
    | TInt (_, attrs) | TEnum (_, attrs) as t ->
      (match Cil.findAttribute Cil.bitfield_attribute_name attrs with
       | [AInt i] -> Int_Base.Value i
       | _ -> Bit_utils.sizeof t)
    | t -> Bit_utils.sizeof t

  let to_value t =
    let loc = Precise_locs.imprecise_location t in
    Locations.loc_to_loc_without_size loc

  let size loc = Precise_locs.loc_size loc

  let offset_cardinal_zero_or_one offset =
    try
      let ival = match offset with
        | Precise off -> Precise_locs.imprecise_offset off
        | Imprecise v -> Cvalue.V.project_ival v
      in
      Ival.cardinal_zero_or_one ival
    with
      Cvalue.V.Not_based_on_null -> false


  exception AlwaysOverlap of Alarms.alarm

  let check_non_overlapping lvs1 lvs2 =
    let conv (lval, loc) =
      let for_writing = false in
      let zone = Precise_locs.enumerate_valid_bits ~for_writing loc in
      let exact =
        lazy (Precise_locs.valid_cardinal_zero_or_one ~for_writing loc)
      in
      lval, zone, exact
    in
    let l1 = List.map conv lvs1
    and l2 = List.map conv lvs2 in
    let check (lval1, zone1, exact1) (lval2, zone2, exact2) acc =
      if Locations.Zone.intersects zone1 zone2
      then
        let alarm = Alarms.Not_separated (lval1, lval2) in
        if Lazy.force exact1 && Lazy.force exact2
        then raise (AlwaysOverlap alarm)
        else Alarmset.add alarm acc
      else acc
    in
    try
      let alarms =
        List.fold_left
          (fun acc x1 -> List.fold_left (fun acc x2 -> check x1 x2 acc) acc l2)
          Alarmset.none
          l1
      in `Value (), alarms
    with AlwaysOverlap alarm -> `Bottom, Alarmset.singleton alarm

  let partially_overlap loc1 loc2 =
    let big_enough size =
      try Integer.gt size (Integer.of_int (Cil.bitsSizeOf Cil.intType))
      with Cil.SizeOfError _ -> true
    in
    let loc1 = Precise_locs.imprecise_location loc1
    and loc2 = Precise_locs.imprecise_location loc2 in
    match loc1.Locations.size with
    | Int_Base.Value size when big_enough size ->
      Locations.(Location_Bits.partially_overlaps size loc1.loc loc2.loc)
    | _ -> false


  (* ------------------------------------------------------------------------ *)
  (*                              Offsets                                     *)
  (* ------------------------------------------------------------------------ *)

  let no_offset = Precise Precise_locs.offset_zero

  let forward_field typ field = function
    | Precise offset ->
      begin try
          let field = fst (Cil.bitsOffset typ (Field (field, NoOffset))) in
          let field_i = Abstract_interp.Int.of_int field in
          Precise (Precise_locs.shift_offset_by_singleton field_i offset)
        with Cil.SizeOfError _ -> Precise (Precise_locs.offset_top)
      end
    | x -> x

  let forward_index typ_pointed index remaining =
    match remaining with
    | Imprecise offset ->
      let bases = Cvalue.V.topify_arith_origin index in
      Imprecise (Cvalue.V.join bases offset)
    | Precise offset ->
      try
        let index_i = Cvalue.V.project_ival index in
        let size = Bit_utils.sizeof typ_pointed in
        (* Index offsets expressed in terms of the array elements size *)
        let index_i =  Ival.scale_int_base size index_i in
        (* Combine the two offsets *)
        Precise (Precise_locs.shift_offset index_i offset)
      with Cvalue.V.Not_based_on_null ->
        (* result will be a garbled mix: collect all the bases involved in
           the evaluation of [offset], and raise an exception *)
        Imprecise (Cvalue.V.topify_arith_origin index)

  (* We are accessing an array of size [size] at indexes [index].
     If index causes an out-of-bounds access, emit an informative
     alarm, and reduce [index]. *)
  let reduce_index_by_array_size ~size_expr ~index_expr size index =
    try
      let index_ival = Cvalue.V.project_ival index in
      let open Abstract_interp in
      let array_range =
        Ival.inject_range (Some Int.zero) (Some (Integer.pred size))
      in
      let new_index = Ival.narrow index_ival array_range in
      if Ival.equal new_index index_ival
      then `Value index, Alarmset.none
      else
        let positive = match Ival.min_int index_ival with
          | None -> false
          | Some min -> Int.ge min Int.zero
        in
        let alarms = Alarmset.singleton
            (Alarms.Index_out_of_bound (index_expr, Some size_expr)) in
        let alarms =
          if not positive
          then Alarmset.add (Alarms.Index_out_of_bound (index_expr, None)) alarms
          else alarms
        in
        if Ival.is_bottom new_index
        then `Bottom, alarms
        else `Value (Cvalue.V.inject_ival new_index), alarms
    with
    | Cvalue.V.Not_based_on_null -> `Value index, Alarmset.none
    (* TODO: reduce the numeric part, and emits the alarms. *)


  (* ------------------------------------------------------------------------ *)
  (*                             Locations                                    *)
  (* ------------------------------------------------------------------------ *)

  let make_precise_loc loc typ_offs =
    let size = sizeof_lval_typ typ_offs in
    let loc = Precise_locs.make_precise_loc loc ~size in
    if Precise_locs.is_bottom_loc loc
    then `Bottom
    else `Value loc

  let join_loc value loc =
    let loc = Locations.(Location_Bits.join loc (loc_bytes_to_loc_bits value)) in
    Precise_locs.inject_location_bits loc

  let forward_variable typ_offset host offset =
    let base = Base.of_varinfo host in
    match offset with
    | Precise offset ->
      let loc_pr = Precise_locs.combine_base_precise_offset base offset in
      make_precise_loc loc_pr typ_offset
    | Imprecise value ->
      let loc_b = Locations.Location_Bits.inject base Ival.zero in
      let loc_pr = join_loc value loc_b in
      make_precise_loc loc_pr typ_offset

  let forward_pointer typ_offset loc_lv offset =
    let loc_bits = Locations.loc_bytes_to_loc_bits loc_lv in
    match offset with
    | Precise offset ->
      let loc_pr = Precise_locs.combine_loc_precise_offset loc_bits offset in
      make_precise_loc loc_pr typ_offset
    | Imprecise value ->
      let loc_pr = join_loc value loc_bits in
      make_precise_loc loc_pr typ_offset

  let eval_varinfo varinfo =
    let loc = Locations.loc_of_varinfo varinfo in
    let loc_bits = Precise_locs.inject_location_bits loc.Locations.loc in
    Precise_locs.make_precise_loc loc_bits ~size:loc.Locations.size

  let is_valid ~for_writing loc =
    Locations.is_valid ~for_writing (Precise_locs.imprecise_location loc)

  let memory_access_alarm ~for_writing lval =
    let access_kind =
      if for_writing then Alarms.For_writing else Alarms.For_reading
    in
    Alarmset.singleton (Alarms.Memory_access (lval, access_kind))

  let reduce_loc_by_validity ~for_writing ~bitfield lval loc =
    if not (is_valid ~for_writing loc)
    then
      let alarms = memory_access_alarm ~for_writing lval in
      let loc = Precise_locs.valid_part ~for_writing ~bitfield loc in
      if Precise_locs.is_bottom_loc loc
      then `Bottom, alarms
      else `Value loc, alarms
    else `Value loc, Alarmset.none

  let backward_pointer location offset =
    let loc_val = to_value location in
    let off_val = match offset with
      | Precise offset ->
        let ival = Precise_locs.imprecise_offset offset in
        let ival = Ival.scale_div ~pos:true (Integer.of_int 8) ival in
        Cvalue.V.inject_ival ival
      | Imprecise value -> value
    in
    let mem = Cvalue.V.add_untyped Int_Base.minus_one loc_val off_val in
    if Cvalue.V.is_bottom mem
    then `Bottom
    else `Value mem

end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
