(**************************************************************************)
(*                                                                        *)
(*  This file is part of tis-interpreter.                                 *)
(*  Copyright (C) 2016 TrustInSoft                                        *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  General Public License as published by the Free Software              *)
(*  Foundation, version 2.                                                *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU General Public License version 2 for more details.                *)
(*  (enclosed in the file licences/GPLv2).                                *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Cvalue
open Abstract_interp
open Locations
open Value_util

(* define helper functions and values*)
module Aux = Builtins_lib_tis_aux
let register_builtin = Aux.register_builtin
let dkey = Aux.dkey

(*  Implementation of [memset] that accepts imprecise arguments. Assumes
    the syntactic context is positioned. *)
let tis_memset_imprecise state dst v size =
  let size_char = Bit_utils.sizeofchar () in
  let with_alarms = warn_all_quiet_mode () in
  let size_min, size_max_bytes =
    try
      let size = Cvalue.V.project_ival size in
      let min,max = Ival.min_and_max size in
      let min = match min with
        | None -> Int.zero
        | Some m -> Int.mul size_char (Int.max m Int.zero)
      and max = match max with
        | None -> Bit_utils.max_bit_address ()
        | Some m -> m
      in min, max
    with V.Not_based_on_null -> Int.zero, Bit_utils.max_bit_address ()
  in
  let left = loc_bytes_to_loc_bits dst in
  (* Write [v] everywhere that might be written, ie between
     [dst] and [dst+size-1]. *)
  let new_state =
    if Int.gt size_max_bytes Int.zero then
      let shift =
        Ival.inject_range (Some Int.zero) (Some (Int.pred size_max_bytes))
      in
      let loc = Location_Bytes.shift shift dst in
      let loc = loc_bytes_to_loc_bits loc in
      let loc = make_loc loc (Int_Base.inject size_char) in
      Eval_op.add_binding ~with_alarms
        ~remove_invalid:true ~exact:false state loc v
    else state
  in
  (* Write "sure" bytes in an exact way: they exist only if there is only
     one base, and within it, size_min+leftmost_loc > rightmost_loc *)
  let new_state' =
    try
      let base, offset = Location_Bits.find_lonely_key left in
      let minb, maxb = match Ival.min_and_max offset with
        | Some minb, Some maxb -> minb, maxb
        | _ -> raise Not_found
      in
      let sure = Int.sub (Int.add minb size_min) maxb in
      if Int.gt sure Int.zero then
        let left' = Location_Bits.inject base (Ival.inject_singleton maxb) in
        let vuninit = V_Or_Uninitialized.initialized v in
        let from = V_Offsetmap.create ~size:sure vuninit ~size_v:size_char in
        Eval_op.paste_offsetmap ~with_alarms ~remove_invalid:true
          ~reducing:false ~from ~dst_loc:left' ~size:sure ~exact:true new_state
      else
        new_state
    with Not_found -> new_state (* from find_lonely_key + explicit raise *)
  in
  { Value_types.c_values = [ Eval_op.wrap_ptr dst, new_state' ];
    c_clobbered = Base.SetLattice.bottom;
    c_cacheable = Value_types.Cacheable;
    c_from = None; (* TODO?*)
  }
(* let () = register_builtin "tis_memset" tis_memset_imprecise *)

(* Type that describes why the 'precise memset' builtin may fail. *)
type imprecise_memset_reason =
| UnsupportedType
| ImpreciseTypeSize
| NoTypeForDest
| NotSingletonLoc
| SizeMismatch
| ImpreciseValue
| ImpreciseSize
| NegativeOrNullSize (* The zero case is licit, but it is simpler to handle
                        through the imprecise builtin. See bts #1799 *)

exception ImpreciseMemset of imprecise_memset_reason

let pretty_imprecise_memset_reason fmt = function
  | UnsupportedType ->
    Format.pp_print_string fmt "destination has an unknown type"
  | ImpreciseTypeSize ->
    Format.pp_print_string fmt "destination has a type with unknown size"
  | NoTypeForDest ->
    Format.pp_print_string fmt "destination has an unknown form"
  | NotSingletonLoc ->
    Format.pp_print_string fmt "destination is not exact"
  | SizeMismatch ->
    Format.pp_print_string fmt "destination type and size differ"
  | ImpreciseValue ->
    Format.pp_print_string fmt "value to write is imprecise"
  | ImpreciseSize ->
    Format.pp_print_string fmt "size is imprecise"
  | NegativeOrNullSize ->
    Format.pp_print_string fmt "size is negative or null"


(*  [memset_typ_offsm typ i] returns an offsetmap of size [sizeof(typ)]
    that maps each byte to the integer [i]. The shape of the type is
    respected: the fields in [typ] are bound to values of the good type,
    not just to 'i%repeated modulo 8'. May raise ImpreciseMemset. *)
let memset_typ_offsm_int full_typ i =
  try
    let size = Int.of_int (Cil.bitsSizeOf full_typ) in
    let vi = V_Or_Uninitialized.initialized (Cvalue.V.inject_int i) in
    let size_char = Bit_utils.sizeofchar () in
    let full_offsm = V_Offsetmap.create ~size vi ~size_v:size_char in
    if Int.is_zero i then
      full_offsm (* Shortcut: no need to follow the type, this offsetmap is
                    optimally precise *)
    else
      let validity = Base.Known (Int.zero, Int.pred size) in
      (* no access error to signal here, given the validity we use. However,
         we want to be notified of float conversion errors. *)
      let alarms_ok = ref true in
      let with_alarms =
        let not_ok () = alarms_ok := false in {
          CilE.others = {CilE.a_ignore with CilE.a_call=not_ok};
          unspecified = {CilE.a_ignore with CilE.a_call=not_ok};
          defined_logic = {CilE.a_ignore with CilE.a_call=not_ok};
          imprecision_tracing = CilE.a_ignore;
        }
      in
      let rec aux styp offset offsm =
        (* Read [full_offsm] between [offset] and [offset+size-1], and return
           the value stored there. *)
        let find size =
          snd (V_Offsetmap.find ~validity
                 ~offsets:(Ival.inject_singleton offset) ~size full_offsm)
        in
        (* Update [full_offsm] between [offset] and [offset+size-1], and store
           exactly [v] there *)
        let update size v =
          let bounds = (offset, Int.(pred (add offset size))) in
          let vinit = V_Or_Uninitialized.initialized v in
          V_Offsetmap.add bounds (vinit, size, Rel.zero) offsm
        in
        match Cil.unrollType styp with
        | TInt _ | TEnum _ | TPtr _ ->
          let size = Eval_typ.sizeof_lval_typ styp (* handles bitfields *) in
          let size = Int_Base.project size in
          let v = V_Or_Uninitialized.get_v (find size) in
          let signed = Bit_utils.is_signed_int_enum_pointer styp in
          let v, _ok = Cvalue.V.cast ~size ~signed v in
          update size v
        | TFloat (fkind, _) ->
          let size = Int.of_int (Cil.bitsSizeOf styp) in
          let v = V_Or_Uninitialized.get_v (find size) in
          (* Use reinterpret_float to get a floating point-value when possible:
             the transfer functions in Ival do not like mismatches
             integer/float. BUT catch errors (is_finite) during the conversion,
             because we prefer having a precise int value instead of a
             bottom/imprecise float .*)
          alarms_ok := true;
          let v' = Eval_op.reinterpret_float ~with_alarms fkind v in
          if !alarms_ok then update size v' else update size v
        | TComp ({ cstruct = true ; cfields = l}, _, _) as tcomp -> (* struct *)
          let aux_field offsm fi =
            let field = Field (fi, NoOffset) in
            let offset_fi = Int.of_int (fst (Cil.bitsOffset tcomp field)) in
            aux fi.ftype (Int.add offset offset_fi) offsm
          in
          List.fold_left aux_field offsm l
        | TComp ({ cstruct = false ; cfields = l}, _, _) -> (* union *)
          (* Use only the first field. This is somewhat arbitrary *)
          aux (List.hd l).ftype offset offsm
        | TArray (typelt, nb, _, _) -> begin
          let nb = Cil.lenOfArray64 nb in (* always succeeds, we computed the
                                             size of the entire type earlier *)
          if Integer.(gt nb zero) then begin
            let sizeelt = Int.of_int (Cil.bitsSizeOf typelt) in
            (* Do the first cell *)
            let offsm' = aux typelt offset offsm in
            if Integer.(gt nb one) then begin
              (* Copy the result *)
              let src = Ival.inject_singleton offset in
              let _alarm_access, copy =
                V_Offsetmap.copy_slice
                  ~validity ~offsets:src ~size:sizeelt offsm'
              in
              (* Paste on all offsets > 1 *)
              let dst =
                let idx =
                  Ival.inject_range (Some Int.one) (Some (Int.pred nb))
                in
                let idx_size = Ival.scale sizeelt idx in
                Ival.add_singleton_int offset idx_size
              in
              match copy with
              | `Bottom -> assert false (* the copy is within bounds *)
              | `Map copy ->
                let _alarm_access, r =
                  V_Offsetmap.paste_slice ~validity
                    ~exact:true ~from:copy ~size:sizeelt ~offsets:dst offsm'
                in
                match r with
                | `Bottom -> assert false (* so is the write *)
                | `Map r -> r
            end
            else offsm' (* size = 1 *)
          end
          else offsm (* size = 0. Do nothing, this is supposed to be invalid
                        anyway *)
        end
        | TVoid _ | TFun _ | TBuiltin_va_list _ ->
          raise (ImpreciseMemset UnsupportedType)
        | TNamed _ -> assert false (* unrolled *)
      in
      aux full_typ Int.zero full_offsm
  with Cil.SizeOfError _ | Int_Base.Error_Top ->
    raise (ImpreciseMemset ImpreciseTypeSize)

(*  Type-aware memset on an entire type. Same as [memset_typ_offsm_int], but
    with a [Cvalue.V] instead of an integer. We accept [-ilevel] different
    possible values in [v] before falling back to the imprecise memset.
    May rais {!ImpreciseMemset}.  *)
let memset_typ_offsm typ v =
  try
    let i = V.project_ival v in
    ignore (Ival.cardinal_less_than i (Ival.get_small_cardinal ()));
    let aux_i i offsm =
      let offsm_i = memset_typ_offsm_int typ i in
      match offsm with
      | None -> Some offsm_i
      | Some o -> Some (Cvalue.V_Offsetmap.join o offsm_i)
    in begin
      match Ival.fold_int aux_i i None with
      | None -> (* v == Ival.bottom *)
        raise (ImpreciseMemset ImpreciseValue)
      | Some o -> o
    end
  with V.Not_based_on_null | Not_less_than ->
    raise (ImpreciseMemset ImpreciseValue)

(*  Precise memset builtin, that requires its arguments to be sufficiently
    precise abstract values. Assumes the syntactic context is positioned. *)
let tis_memset_precise state dst v (exp_size, size) =
  try
    let size_char = Bit_utils.sizeofchar () in
    (* We want an exact size, Otherwise, we can use the imprecise memset as a
       fallback *)
    let isize = V.project_ival size in
    let size = Ival.project_int isize in
    let size_bits = Integer.mul size_char size in
    (* Extract the location, check that it is precise. *)
    if not (Location_Bytes.cardinal_zero_or_one dst) then
      raise (ImpreciseMemset NotSingletonLoc);
    if not (Int.gt size Int.zero) then
      raise (ImpreciseMemset NegativeOrNullSize);
    (* Now, try to find a type that matches [size]. *)
    let typ =
      (* If [exp_size] is a sizeof, use this type. *)
      let rec find_sizeof e = match e.enode with
        | SizeOf typ -> Some typ
        | SizeOfE e -> Some (Cil.typeOf e)
        | CastE (_, e) -> find_sizeof e
        | _ -> None
      in
      match find_sizeof exp_size with
      | Some typ -> typ
      | None ->
        (* No such luck. Use the base and the offset of [dst] to resynthesize
           a type *)
        let base_dst, offset_dst = Location_Bytes.find_lonely_binding dst in
        let offset_dst = Ival.project_int offset_dst in
        let offset_dst_bits = Int.mul offset_dst size_char in
        let vi_dst = Base.to_varinfo base_dst in
        let mo = Bit_utils.MatchSize size_bits in
        snd (Bit_utils.(find_offset vi_dst.vtype offset_dst_bits mo))
    in
    let offsm = memset_typ_offsm typ v in
    let dst_loc = Locations.loc_bytes_to_loc_bits dst in
    let with_alarms = warn_all_quiet_mode () in
    let state' =
      Eval_op.paste_offsetmap ~with_alarms ~remove_invalid:true
        ~reducing:false ~from:offsm ~dst_loc ~size:size_bits ~exact:true state
    in
    { Value_types.c_values = [Eval_op.wrap_ptr dst, state'];
      c_clobbered = Base.SetLattice.bottom;
      c_cacheable = Value_types.Cacheable;
      c_from = None; (* TODO?*)
    }
  with
  | Bit_utils.NoMatchingOffset -> raise (ImpreciseMemset SizeMismatch)
  | Base.Not_a_C_variable -> raise (ImpreciseMemset NoTypeForDest)
  | Cil.SizeOfError _ -> raise (ImpreciseMemset ImpreciseTypeSize)
  | Ival.Not_Singleton_Int | V.Not_based_on_null ->
    raise (ImpreciseMemset ImpreciseSize)

(* let () = register_builtin "tis_memset_precise" tis_memset_precise *)

let tis_memset state actuals =
  if Value_parameters.ValShowProgress.get () then
    Value_parameters.feedback ~current:true "Call to builtin memset(%a)%t"
      pretty_actuals actuals Value_util.pp_callstack;
  match actuals with
    | [(exp_dst, dst, _) as actual; (_exp_v, v, _); (exp_size, size, _)] ->
      begin
        Aux.additional_ptr_validity_check_for_size_zero ~for_writing:true ~size actual;
        (* Position syntactic context *)
        let term_size = Logic_utils.expr_to_term ~cast:true exp_size in
        let array_dst = Logic_utils.array_with_range exp_dst term_size in
        Valarms.set_syntactic_context (Valarms.SyMemLogic array_dst);
        (* Keep only the first byte of the argument *)
        let _, v = Cvalue.V.extract_bits
          ~topify:Origin.K_Misalign_read
          ~start:Int.zero ~stop:(Int.pred (Bit_utils.sizeofchar ()))
          ~size:(Int.of_int (Cil.bitsSizeOfInt IInt))
          v
        in
        try
          tis_memset_precise state dst v (exp_size, size)
        with ImpreciseMemset reason ->
          Value_parameters.debug ~dkey ~current:true
            "Call to builtin precise_memset(%a) failed; %a%t"
            pretty_actuals actuals pretty_imprecise_memset_reason reason
            Value_util.pp_callstack;
          tis_memset_imprecise state dst v size
      end
    | _ ->
        Value_parameters.result
          "Invalid call to tis_memset builtin %a%t"
          pretty_actuals actuals Value_util.pp_callstack;
        raise Db.Value.Aborted

let () = register_builtin "tis_memset" tis_memset
