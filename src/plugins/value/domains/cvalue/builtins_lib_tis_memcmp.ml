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

open Cvalue
open Abstract_interp
open Locations
open Value_util

(* define helper functions *)
module Aux = Builtins_lib_tis_aux
let register_builtin = Aux.register_builtin

let make_with_alarms r =
  let emit = { CilE.a_log = false; CilE.a_call = r } in
  { CilE.imprecision_tracing = CilE.a_ignore;
    defined_logic = emit;
    unspecified =   emit;
    others =        emit;
  }

exception Alarm
let raise_alarm () = raise Alarm
let with_alarms_raise = make_with_alarms raise_alarm

exception DontKnow

let abstract_memcmp ~size ~signed ~emit_alarm mem1 syn1 mem2 syn2 n synn state =
  (* Checks whether the call to memcmp respects the preconditions:
     Calls emit_alarm syn? (e.g. \valid(..) && \forall.. \base_addr(..)
     if anything at all is wrong.
  *)

  let n, n_addr = Cvalue.V.split Base.null n in
  if not (Cvalue.V.is_bottom n_addr)
  then begin
    Value_parameters.warning ~current:true
      "memcmp() seems to be passed a mix of addresses and \
                  integers for size argument; assert(%a an integer)%t"
      Cil_datatype.Exp.pretty synn
      Value_util.pp_callstack;
    (* TODO: add alarm (need to add a new alarm type?) *)
  end;
  if (Ival.is_bottom n) then Ival.bottom
  else
  try begin
  match mem1, mem2 with
  | Location_Bytes.Top _, _ | _, Location_Bytes.Top _ ->
    raise DontKnow
  | Location_Bytes.Map _, Location_Bytes.Map _ ->
    let negative_res = ref false in
    let positive_res = ref false in
    let zero_res = ref false in
    let size_size = Int_Base.inject size in
    let size_ival = Ival.inject_singleton size in
    let min, max =
      match Ival.min_and_max n with
      | Some min, Some max -> min, max
      | _ -> raise DontKnow
    in
    let min_total_size =
      Int_Base.inject
        (if Int.is_zero min then Int.one else Int.mul size min)
    in
    let locbb1 = Locations.loc_bytes_to_loc_bits mem1 in
    let locb1 =
      let locmin = make_loc locbb1 min_total_size in
      (valid_part ~for_writing:false locmin).loc
    in
    let locbb2 = Locations.loc_bytes_to_loc_bits mem2 in
    let locb2 =
      let locmin = make_loc locbb2 min_total_size in
      (valid_part ~for_writing:false locmin).loc
    in
    let warn1 = ref (not (Location_Bits.equal locb1 locbb1)) in
    let warn2 = ref (not (Location_Bits.equal locb2 locbb2)) in
    let set_warn1 () = warn1 := true in
    let set_warn2 () = warn2 := true in
    let with_alarms1 = make_with_alarms set_warn1 in
    let with_alarms2 = make_with_alarms set_warn2 in
    let read_char warn with_alarms lobc (chars_acc, locb_acc as acc) =
      let loc = Locations.make_loc lobc size_size in
      let char, address =
        let char = Eval_op.find ~with_alarms state loc in
        Cvalue.V.split Base.null char
      in
      if not (Cvalue.V.is_bottom address) then warn ();
      if Ival.is_bottom char
      then acc
      else begin
        let char = Ival.cast ~size ~signed ~value:char in
        Ival.join char chars_acc,
        Location_Bits.join loc.Locations.loc locb_acc
      end
    in
    let detect_alarm_after_i warn locb i =
      let rec aux locb i =
        if (Int.lt i max)
        then
          let acc = Ival.top, Location_Bits.bottom in
          let _, locb =
            Location_Bits.fold_enum
              (read_char raise_alarm with_alarms_raise)
              locb
              acc
          in
          aux (Location_Bits.shift size_ival locb) (Int.succ i)
      in
      try
        if not !warn then aux locb i
      with Alarm -> warn := true
    in
    let rec iterate i locb1 locb2 =
      if Int.equal i min then zero_res := true;
      if Int.lt i max
      then
        let acc = Ival.bottom, Location_Bits.bottom in
        let chars1, new_locb1 =
          Location_Bits.fold_enum
            (read_char set_warn1 with_alarms1)
            locb1
            acc
        in
        let chars2, new_locb2 =
          Location_Bits.fold_enum
            (read_char set_warn2 with_alarms2)
            locb2
            acc
        in
        let new_locb1 = Location_Bits.shift size_ival new_locb1 in
        let new_locb2 = Location_Bits.shift size_ival new_locb2 in
        let new_i = Integer.succ i in
(*      Format.printf "iteration %a: %a %a %a %a %B %B@."
         Int.pretty i
         Ival.pretty chars1 Ival.pretty chars2
         Location_Bits.pretty new_locb1
         Location_Bits.pretty new_locb2
         !warn1 !warn2; *)
        if Ival.is_bottom chars1 || Ival.is_bottom chars2 ||
          (!negative_res && !positive_res && !zero_res)
        then begin
          detect_alarm_after_i warn1 new_locb1 new_i;
          detect_alarm_after_i warn2 new_locb2 new_i;
          (* exit loop immediately *)
        end
        else
          let min1, max1 = Ival.min_and_max chars1 in
          let min2, max2 = Ival.min_and_max chars2 in
          if Ival.compare_min_max min1 max2 < 0 then negative_res := true;
          if Ival.compare_min_max min2 max1 < 0 then positive_res := true;
(*        Format.printf "iteration--- pos:%B zero:%B neg:%B@." !positive_res
           !zero_res !negative_res; *)
          if not (Ival.intersects chars1 chars2)
          then begin
            detect_alarm_after_i warn1 new_locb1 new_i;
            detect_alarm_after_i warn2 new_locb2 new_i;
            (* exit loop immediately *)
          end
          else begin
          (* continue the loop *)
            iterate new_i new_locb1 new_locb2
          end;
    in
    iterate Int.zero locb1 locb2;
    if !warn1 then emit_alarm syn1;
    if !warn2 then emit_alarm syn2;
    let res =
      if !zero_res
      then Ival.zero
      else Ival.bottom
    in
    let res = if !positive_res then Ival.join Ival.one res else res in
    if !negative_res then Ival.join Ival.minus_one res else res
  end
  with DontKnow ->
    emit_alarm syn1;
    emit_alarm syn2;
    Ival.join Ival.minus_one Ival.zero_or_one

let tis_memcmp name ~size ~signed state actuals =
  if Value_parameters.ValShowProgress.get () then
    Value_parameters.feedback ~current:true "Call to builtin %s(%a)%t"
      name
      pretty_actuals actuals Value_util.pp_callstack;
  match actuals with
    | [ (exp1, mem1, _) as a1; (exp2, mem2, _) as a2; expn, n, _ ] ->
      let emit_alarm syn =
        let term_size = Logic_utils.expr_to_term ~cast:true expn in
        let array = Logic_utils.array_with_range syn term_size in
        Valarms.set_syntactic_context (Valarms.SyMemLogic array);
        Valarms.warn_mem_read (warn_all_quiet_mode ())
      in
      Aux.additional_ptr_validity_check_for_size_zero ~for_writing:false ~size:n a1;
      Aux.additional_ptr_validity_check_for_size_zero ~for_writing:false ~size:n a2;
      let value =
        abstract_memcmp ~size ~signed
          ~emit_alarm mem1 exp1 mem2 exp2 n expn state
      in
      if Ival.is_bottom value
      then
        { Value_types.c_values = [ None, Cvalue.Model.bottom];
          c_clobbered = Base.SetLattice.bottom;
          c_cacheable = Value_types.Cacheable;
          c_from = None; (* TODO?*)
        }
      else
      { Value_types.c_values = [ Eval_op.wrap_int (V.inject_ival value), state ];
        c_clobbered = Base.SetLattice.bottom;
        c_cacheable = Value_types.Cacheable;
        c_from = None; (* TODO?*)
      }
    | _ ->
      raise Db.Value.Aborted

let () = register_builtin "tis_memcmp"
  (tis_memcmp "memcmp" ~signed:false ~size:(Bit_utils.sizeofchar ()))


(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
