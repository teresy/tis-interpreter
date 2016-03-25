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

(** Abstract memory locations of the analysis. *)

open Cil_types
open Eval


(** Signature of abstract memory locations. *)
module type S = sig
  type value

  type location  (** abstract locations *)
  type offset    (** abstract offsets *)

  val to_value : location -> value
  val size : location -> Int_Base.t

  val partially_overlap: location -> location -> bool

  (** Needed for unspecified sequences. *)
  val check_non_overlapping:
    (lval * location) list -> (lval * location) list -> unit evaluated

  (** Needed for Evaluation.get_influential_vars *)
  val offset_cardinal_zero_or_one: offset -> bool

  (** {3 Forward Offset Operations } *)

  val no_offset : offset

  (** Computes the field offset of a fieldinfo, with the given remaining offset.
      The given type must the one of the structure or the union. *)
  val forward_field : typ -> fieldinfo -> offset -> offset

  (** [forward_index typ value offset] computes the array index offset of
      (Index (ind, off)), where the index expression [ind] evaluates to [value]
      and the remaining offset [off] evaluates to [offset].
      [typ] must be the type pointed by the array. *)
  val forward_index : typ -> value -> offset -> offset

  (** [reduce_index_by_array_size ~size_expr ~index_expr size index] reduces
      the value [index] to fit into the inverval [0..(size-1)]. It also returns
      out-of-bound alarms if it was not already the case. [size_expr] and
      [index_expr] are the Cil expressions of the array size and the index,
      needed to create the alarms. *)
  val reduce_index_by_array_size :
    size_expr: exp -> index_expr: exp -> Integer.t -> value -> value evaluated

  (** {3 Forward Locations Operations } *)

  (** Evaluation of the location of an lvalue, when the offset has aleardy
      been evaluated. In case of a pointer, its expression has also been
      evaluated to a value. *)

  val forward_variable : typ -> varinfo -> offset -> location or_bottom
  val forward_pointer : typ -> value -> offset -> location or_bottom

  val eval_varinfo : varinfo -> location

  (** [reduce_loc_by_validity for_writing bitfield lval loc] reduce the location
      [loc] by its valid part for a read or write operation, according to the
      [for_writing] boolean. It also returns the alarms enusuring this validity.
      [bitfield] indicates whether the location may be the one of a bitfield;
      if it does not hold, the location is assumed to be byte aligned.
      [lval] is only used to create the alarms. *)
  val reduce_loc_by_validity :
    for_writing:bool -> bitfield:bool -> lval -> location -> location evaluated

  (** {3 Backward Operations } *)

  (** [backward_pointer location offset] computes the value of the pointer,
      given the final location and the offset.*)
  val backward_pointer : location -> offset -> value or_bottom
end

(** Key and structure for locations. See {structure.mli},
    and {domain.mli} where the mechanism is explained in detail.*)

type 'a key = 'a Structure.Key_Location.k
type 'a structure = 'a Structure.Key_Location.structure

module type Internal = sig
  include S
  val structure : location structure
end

module type External = sig
  include S
  include Structure.External with type t := location
                              and type 'a key := 'a key
end

(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
