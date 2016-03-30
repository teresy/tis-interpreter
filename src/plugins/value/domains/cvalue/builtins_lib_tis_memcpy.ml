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
open Builtins_lib_tis_aux (* overlap status *)

exception Memcpy_result of Cvalue.Model.t
exception Indeterminate of V_Or_Uninitialized.t
exception Do_Bottom

module Aux = Builtins_lib_tis_aux
let register_builtin = Builtins.register_builtin
let dkey = Value_parameters.register_category "imprecision"

open Aux.StringAndArrayUtilities

type memcpy_alarm_context = {
  (* The warn mode. *)
  memcpy_alarm_warn_mode : CilE.warn_mode;
  (* Function setting the syntactic context to the source. *)
  memcpy_alarm_set_syntactic_context_array_src : unit -> unit;
  (* Function setting the syntactic context to the destination. *)
  memcpy_alarm_set_syntactic_context_array_dst : unit -> unit
}

(* Alarm context used when necessary information about source and destination
   is hard to get. *)
let memcpy_alarm_context_none = {
  memcpy_alarm_warn_mode = (CilE.warn_none_mode);
  memcpy_alarm_set_syntactic_context_array_src = (fun () -> ());
  memcpy_alarm_set_syntactic_context_array_dst = (fun () -> ())
}

let abstract_memcpy ?(exact=true) ~(character_bits : Integer.t) ~emit_alarm
  ~(size: Ival.t) (* Number of characters to copy. *)
  (src : Location_Bytes.t) (dst : Location_Bytes.t) (state : Model.t) : Model.t =

  let with_alarms = emit_alarm.memcpy_alarm_warn_mode in

  let min,_ = Ival.min_and_max size in
  let min = match min with None -> Int.zero | Some m -> Int.max m Int.zero in
  let size_min = Int.mul character_bits min in

  let right = loc_bytes_to_loc_bits src in
  let left = loc_bytes_to_loc_bits dst in

  if Ival.is_zero size
  then state
  else begin
    emit_alarm.memcpy_alarm_set_syntactic_context_array_src ();
    match Eval_op.copy_offsetmap ~with_alarms right size_min state with
    | `Map offsetmap ->
       (* Read succeeded. We write the result *)
       emit_alarm.memcpy_alarm_set_syntactic_context_array_dst ();
      Eval_op.paste_offsetmap ~with_alarms ~remove_invalid:true
        ~reducing:false ~from:offsetmap ~dst_loc:left ~size:size_min
        ~exact:exact state
    | `Top
    | `Bottom -> assert false
  end


(* Implements built-ins:
   - tis_memcpy
   - tis_wmemcpy
   - tis_memmove
   - tis_wmemmove *)
let tis_memcpy ~str_or_wcs ~check_overlap state actuals =
  let builtin_name =
    match check_overlap, str_or_wcs with
    | true,  Character     -> "memcpy"
    | true,  WideCharacter -> "wmemcpy"
    | false, Character     -> "memmove"
    | false, WideCharacter -> "wmemmove"
  in
  let compute ((exp_dst,dst,_) as a1) ((exp_src,src,_) as a2) (exp_size,size,_) =
    if Value_parameters.ValShowProgress.get () then
      Value_parameters.feedback ~current:true "Call to builtin tis_%s(%a)%t"
        builtin_name pretty_actuals actuals Value_util.pp_callstack;
    Aux.additional_ptr_validity_check_for_size_zero ~for_writing:true ~size a1;
    Aux.additional_ptr_validity_check_for_size_zero ~for_writing:false ~size a2;

    let size =
      try Cvalue.V.project_ival size
      with Cvalue.V.Not_based_on_null -> Ival.top
    in
    let character_bits = get_character_bits str_or_wcs in
    let right = loc_bytes_to_loc_bits src in
    let left = loc_bytes_to_loc_bits dst in

    let term_size = Logic_utils.expr_to_term ~cast:true exp_size in
    let array_src = Logic_utils.array_with_range exp_src term_size in
    let array_dst = Logic_utils.array_with_range exp_dst term_size in

    if check_overlap then
      begin
        match overlap_status_loc_bits ~size_in_bytes:true left size right size
        with
        | Overlap ->
          Value_parameters.error ~current:true
            "overlapping memory zones in call to %s(%a, %a, %a); \
             assert(no overlap between source and destination objects). \
             Will return bottom for this execution path."
            builtin_name
            Cil_datatype.Term.pretty array_src
            Cil_datatype.Term.pretty array_dst
            Cil_datatype.Term.pretty term_size;
          raise Do_Bottom
        | MayOverlap ->
          Value_parameters.warning ~current:true
            "possible overlapping memory zones in call to %s(%a, %a, %a); \
             assert(no overlap between source and destination objects)."
            builtin_name
            Cil_datatype.Term.pretty array_src
            Cil_datatype.Term.pretty array_dst
            Cil_datatype.Term.pretty term_size
        (** TODO: Add assert message **)
        | Separated -> ()
      end;

    let new_state =
      let emit_alarm = {
        memcpy_alarm_warn_mode =
          (warn_all_quiet_mode ());
        memcpy_alarm_set_syntactic_context_array_src =
          (fun () -> Valarms.set_syntactic_context (Valarms.SyMemLogic array_src));
        memcpy_alarm_set_syntactic_context_array_dst =
          (fun () -> Valarms.set_syntactic_context (Valarms.SyMemLogic array_dst))
      }
      in
      abstract_memcpy ~emit_alarm ~character_bits ~size src dst state
    in
      if Model.is_reachable new_state then
        (* Copy at least partially succeeded (with perhaps an
           alarm for some of the sizes *)
        { Value_types.c_values = [ Eval_op.wrap_ptr dst, new_state ];
          c_clobbered = Location_Bits.get_bases left;
          c_cacheable = Value_types.Cacheable;
          c_from = None; (* TODO?*)
        }
      else
        { Value_types.c_values = [ None, Cvalue.Model.bottom];
          c_clobbered = Base.SetLattice.bottom;
          c_cacheable = Value_types.Cacheable;
          c_from = None; (* TODO?*)
        }
  in
  try
    match actuals with
    | [dst; src; size] -> compute dst src size
    | _ -> raise Db.Value.Aborted
  with
  | V.Not_based_on_null
  | Db.Value.Outside_builtin_possibilities as e ->
    Value_parameters.result
      "Invalid call to tis_%s builtin %a%t"
      builtin_name pretty_actuals actuals Value_util.pp_callstack;
    raise e
  | Db.Value.Aborted ->
    Value_parameters.error
      "Invalid call to tis_%s%a"
      builtin_name pretty_actuals actuals;
    raise Db.Value.Aborted
  | Do_Bottom ->
    { Value_types.c_values = [ None, Cvalue.Model.bottom];
      c_clobbered = Base.SetLattice.bottom;
      c_cacheable = Value_types.Cacheable;
      c_from = None; (* TODO?*)
    }

let () = register_builtin "tis_memcpy"   (tis_memcpy ~str_or_wcs:Character     ~check_overlap:true)
let () = register_builtin "tis_wmemcpy"  (tis_memcpy ~str_or_wcs:WideCharacter ~check_overlap:true)
let () = register_builtin "tis_memmove"  (tis_memcpy ~str_or_wcs:Character     ~check_overlap:false)
let () = register_builtin "tis_wmemmove" (tis_memcpy ~str_or_wcs:WideCharacter ~check_overlap:false)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
