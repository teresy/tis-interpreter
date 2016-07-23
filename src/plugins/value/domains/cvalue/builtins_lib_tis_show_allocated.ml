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

(* Builtin for printing allocated variables. *)

open Cvalue


let tis_show_allocated state args =
  match args with
  | [] ->
        ( match state with
        | Model.Bottom | Model.Top -> assert false
        | Model.Map m ->
          Value_parameters.result ~current:true ~once:false
            "remaining allocated variables:@\n  @[%a@]"
            (fun fmt ->
              let sep = ref "" in
              Model.iter
                (fun base _ ->
                  match base with
                  | Base.Allocated (v,_) ->
                    Format.fprintf fmt "%s%a" !sep Printer.pp_varinfo v;
                    sep := ",@ "
                  | _ -> ()))
            m);
        { Value_types.c_values = [ (None, state) ];
          c_clobbered = Base.SetLattice.bottom;
          c_cacheable = Value_types.Cacheable;
          c_from = None; (* TODO?*)
        }
  | _ ->
    Value_parameters.error ~current:true
      "tis_show_allocated() expects void%t"
      Value_util.pp_callstack;
    raise Db.Value.Aborted



let () =
  Builtins.register_builtin "tis_show_allocated" tis_show_allocated;


(*
  Local Variables:
  compile-command: "make -C ../../../../.."
  End:
*)
