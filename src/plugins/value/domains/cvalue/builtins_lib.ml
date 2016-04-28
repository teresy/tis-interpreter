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

let register_builtin = Builtins.register_builtin

let frama_c_copy_block state actuals =
  if Value_parameters.ValShowProgress.get () then
    Value_parameters.feedback ~current:true "Call to builtin copy_block(%a)%t"
      pretty_actuals actuals Value_util.pp_callstack;
  match actuals with
  | [(_, block, _); (_, size,_); (_, length,_)] ->
     let size = Ival.project_int (V.project_ival size) in
     let size = Int.mul size (Bit_utils.sizeofchar()) in
     let length = Ival.project_int (V.project_ival length) in
     let start = loc_bytes_to_loc_bits block in
     let with_alarms = CilE.warn_none_mode in
     let offsetmap =
       Eval_op.copy_offsetmap ~with_alarms start size state
     in
     ( match offsetmap with
     | `Bottom -> assert false
     | `Top -> Warn.warn_top ();
     | `Map offsetmap ->
        let size_ival = Ival.inject_singleton size in
	let state = ref state in
	let dest = ref start in
	let i = ref Int.one in
        while Int.lt !i length do
	  dest := Location_Bits.shift size_ival !dest;
          state :=
          Eval_op.paste_offsetmap ~with_alarms ~remove_invalid:true
          ~reducing:false ~from:offsetmap ~dst_loc:!dest ~size
            ~exact:true !state;
	  i := Int.succ !i;
	done;
        { Value_types.c_values = [None, !state];
          c_clobbered =  Base.SetLattice.bottom;
          c_from = None;
          c_cacheable = Value_types.Cacheable; })
  | _ -> raise (Builtins.Invalid_nb_of_args 3)

let () = register_builtin "Frama_C_copy_block" frama_c_copy_block


(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
