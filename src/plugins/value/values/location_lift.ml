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

open Eval

module type Conversion = sig
  type extended_value
  type internal_value

  val extend_val : internal_value -> extended_value
  val restrict_val : extended_value -> internal_value
end

module Make
    (Loc: Abstract_location.Internal)
    (Convert : Conversion with type internal_value := Loc.value)
= struct

  type value = Convert.extended_value
  type location = Loc.location
  type offset = Loc.offset

  let structure = Loc.structure

  let to_value loc = Convert.extend_val (Loc.to_value loc)
  let size = Loc.size

  let partially_overlap = Loc.partially_overlap
  let check_non_overlapping = Loc.check_non_overlapping
  let offset_cardinal_zero_or_one = Loc.offset_cardinal_zero_or_one
  let no_offset = Loc.no_offset
  let forward_field = Loc.forward_field
  let forward_index typ value offset =
    Loc.forward_index typ (Convert.restrict_val value) offset

  let reduce_index_by_array_size ~size_expr ~index_expr size value =
    let v = Convert.restrict_val value in
    Loc.reduce_index_by_array_size ~size_expr ~index_expr size v >>=: fun v ->
    Convert.extend_val v

  let forward_variable = Loc.forward_variable
  let forward_pointer typ value offset =
    Loc.forward_pointer typ (Convert.restrict_val value) offset
  let eval_varinfo = Loc.eval_varinfo

  let reduce_loc_by_validity = Loc.reduce_loc_by_validity

  let backward_pointer loc offset =
    Loc.backward_pointer loc offset >>-: Convert.extend_val

end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
