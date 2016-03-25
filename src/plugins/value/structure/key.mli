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

type (_,_) eq = Eq : ('a,'a) eq

module type Map = sig
  type 'a key
  type 'a data
  type map
  val empty : map
  val add : 'a key -> 'a data -> map -> map
  val find : 'a key -> map -> 'a data option
end

module type S = sig

  type 'a k

  val create_key: string -> 'a k

  val print: 'a k Pretty_utils.formatter
  val compare: 'a k -> 'b k -> int
  val equal: 'a k -> 'b k -> bool
  val hash : 'a k -> int
  val tag: 'a k -> int

  val iter : ('a k -> unit) -> unit
  val hint_size : unit -> int

  val eq_type : 'a k -> 'b k -> ('a,'b) eq option

  module MkVector (D: sig type ('a,'b) t end)
    : Vector_hetero.S1 with type 'a key = 'a k
                        and type ('a,'b) data = ('a,'b) D.t

  module Vector  : Vector_hetero.R1 with type 'a key = 'a k
  module VectorH : Vector_hetero.T1 with type 'a key = 'a k

  module MkMap (Data : sig type 'a t end) : Map with type 'a key := 'a k
                                                 and type 'a data := 'a Data.t
end

module Make (X: sig end) : S

