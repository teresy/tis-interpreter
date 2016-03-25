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

(** Declarations that are useful for plugins written on top of the results
    of Value. *)

open Cil_types

(* TODO: These types are already defined in Value_util. *)
type call_site = kernel_function * kinstr
type callstack = call_site list
(** Value callstacks, as used e.g. in Db.Value hooks *)

module Callsite: Datatype.S_with_collections with type t = call_site
module Callstack: Datatype.S_with_collections with type t = callstack

(*

  The Shared_callstack module provides more sharing for callstacks. It
  does so by plugging itself in some callstack producers. Currently,
  only the Value_util.call_stack hidden reference is updated.

  Ideally we would like the callstack type to be abstract and
  hash-consed. This change would impact a lot of places, so this
  module may be used to do a soft transition by updating only
  callstack producers to use this abstract type internally but provide
  the concrete callstack type. As long as callstack users do not touch
  these callstacks, they will remain shared and the memory footprint
  will be smaller.

*)
module Shared_callstack : sig

  (* Abstract type for shared callstacks. *)
  type t

  (* [empty] is the equivalent of [[]]. *)
  val empty : t

  (* [push c cs] is the equivalent of [c :: cs]. *)
  val push : call_site -> t -> t (* O(1) *)

  (* [pop cs] is the equivalent of [List.tl cs].
     [cs] must not be empty. *)
  val pop : t -> t (* O(1) *)

  (* [get cs] returns the concrete version of [cs]. *)
  val get : t -> callstack (* O(1) *)

  (* [put cs] returns the abstract version of [cs]. *)
  val put : callstack -> t (* O(n) *)
end

type 'a callback_result =
  | Normal of 'a
  | NormalStore of 'a * int
  | Reuse of int

type cacheable =
  | Cacheable (** Functions whose result can be safely cached *)
  | NoCache (** Functions whose result should not be cached, but for
                which the caller can still be cached. Typically, functions
                printing something during the analysis. *)
  | NoCacheCallers (** Functions for which neither the call, neither the
                       callers, can be cached *)


(** Results of a a call to a function *)
type call_result = {
  c_values: (** Memory states after the call *)
    (Cvalue.V_Offsetmap.t option
       (** the value returned (ie. what is after the 'return' C keyword). *)
     * Cvalue.Model.t
       (** the memory state after the function has been executed *))
    list;

  c_clobbered: Base.SetLattice.t
    (** An over-approximation of the bases in which addresses of local
        variables might have been written *);

  c_cacheable: cacheable
    (** Is it possible to cache the result of this call? *);

  c_from: (Function_Froms.froms * Locations.Zone.t) option
    (** If not None, the froms of the function, and its sure outputs;
        i.e. the dependencies of the result, and the dependencies
        of each zone written to. *)
}


(** Dependencies for the evaluation of a term or a predicate: for each
    program point involved, sets of zones that must be read *)
type logic_dependencies = Locations.Zone.t Cil_datatype.Logic_label.Map.t

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)

