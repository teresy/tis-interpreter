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

(** Abstract numeric values of the analysis. *)

open Cil_types
open Eval

(** Signature of abstract numerical values. *)
module type S = sig
  include Datatype.S

  (** {3 Lattice Structure} *)

  val top : t
  val is_included : t -> t -> bool
  val join : t -> t -> t
  val join_and_is_included : t -> t -> t * bool
  val narrow : t -> t -> t or_bottom

  (** {3 Constructors } *)

  val zero: t
  val float_zeros: t
  val top_int : t
  val inject_int : Abstract_interp.Int.t -> t

  (** Creates all abstract values corresponding to the given type. *)
  val all_values : typ -> t

  (** {3 Forward Operations } *)

  (** Returns the abstract value of a litteral constants, and potentially some
      alarms in case of floating point constants overflow. *)
  val constant : exp -> constant -> t evaluated

  (** [forward_unop context typ unop v] evaluates the value [unop v], and the
      alarms resulting from the operations. See {eval.mli} for details on the
      types. [typ] is the type of [v], and [context] contains the expressions
      involved in the operation, needed to create the alarms. *)
  val forward_unop : context:unop_context -> typ -> unop -> t -> t evaluated

  (** [forward_binop context typ binop v1 v2] evaluates the value [v1 binop v2],
      and the alarms resulting from the operations. See {eval.mli} for details
      on the types. [typ] is the type of [v1], and [context] contains the
      expressions involved in the operation, needed to create the alarms. *)
  val forward_binop : context:binop_context -> typ -> binop -> t -> t -> t evaluated

  (** {3 Backward Operations } *)

  (** [backward_binop ~input_type ~resulting_type binop ~left:v1 ~right:v2 ~result:v]
      returns `Bottom if the operations [v1 binop v2] can not return the value [v],
      or `Value (v1', v2'), where:
      - v1' ⊆ v1
      - v2' ⊆ v2
      - [v1' binop v2'] ⊆ [v]

      [v1'] (resp [v2']) can be None if the value [v1] (resp [v2]) can not
      be reduced (in which case v1' = v1). *)
  val backward_binop : input_type:typ -> resulting_type:typ ->
    binop -> left:t -> right:t -> result:t -> (t option * t option) or_bottom

  val backward_unop :
    typ_arg:typ -> unop -> arg:t -> res:t -> t option or_bottom

  val backward_cast:
    src_typ: typ ->
    dst_typ: typ ->
    src_val: t ->
    dst_val: t ->
    t option or_bottom

  (** {3 Reinterpret and Cast } *)

  (** Read the given value with the given type. Also returns an alarm if the
      type is floating-point type, and the value is not representable as
      finite float. *)
  val reinterpret : exp -> typ -> t -> t evaluated

  val do_promotion : src_typ:typ -> dst_typ: typ -> exp -> t -> t evaluated

  val resolve_functions :
    typ_pointer:typ -> t -> Kernel_function.Hptset.t Eval.or_top * bool
  (** [resolve_functions ~typ_pointer v] finds within [v] all the functions
      with a type compatible with [typ_pointer]. This function is used
      to resolve pointers calls. For consistency between analyses, the function
      {!Eval_typ.compatible_functions} should be used to determine whether the
      functions [v] may point to are compatible with [typ_pointer]. *)

end

(** Key and structure for values. See {structure.mli},
    and {domain.mli} where the mechanism is explained in detail.*)

type 'a key = 'a Structure.Key_Value.k
type 'a structure = 'a Structure.Key_Value.structure

module type Internal = sig
  include S
  val structure : t structure
end

module type External = sig
  include S
  include Structure.External with type t := t
                              and type 'a key := 'a key
end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
