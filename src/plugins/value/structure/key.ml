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

module MkMap
    (Key : sig
       type 'a t
       val compare: 'a t -> 'b t -> int
       val eq_type : 'a t -> 'b t -> ('a, 'b) eq option
     end)
    (Data : sig type 'a t end)
= struct

  type map =
    | Empty : map
    | Node : map * 'a Key.t * 'a Data.t * map * int -> map

  let empty = Empty

  let height = function
    | Empty -> 0
    | Node (_, _, _, _, h) -> h

  let create l x d r =
    let hl = height l and hr = height r in
    Node (l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

  let bal l x d r =
    let hl = match l with Empty -> 0 | Node (_, _, _, _, h) -> h in
    let hr = match r with Empty -> 0 | Node (_, _, _, _, h) -> h in
    if hl > hr + 2 then begin
      match l with
      | Empty -> invalid_arg "Map.bal"
      | Node (ll, lv, ld, lr, _) ->
        if height ll >= height lr then
          create ll lv ld (create lr x d r)
        else begin
          match lr with
          | Empty -> invalid_arg "Map.bal"
          | Node  (lrl, lrv, lrd, lrr, _) ->
            create (create ll lv ld lrl) lrv lrd (create lrr x d r)
        end
    end else if hr > hl + 2 then begin
      match r with
      | Empty -> invalid_arg "Map.bal"
      | Node (rl, rv, rd, rr, _) ->
        if height rr >= height rl then
          create (create l x d rl) rv rd rr
        else begin
          match rl with
          | Empty -> invalid_arg "Map.bal"
          | Node (rll, rlv, rld, rlr, _) ->
            create (create l x d rll) rlv rld (create rlr rv rd rr)
        end
    end else
      Node (l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

  let rec add key data = function
    | Empty -> Node (Empty, key, data, Empty, 1)
    | Node (left, k, d, right,  h) ->
      let c = Key.compare key k in
      if c = 0 then
        Node (left, key, data, right, h)
      else if c < 0 then
        bal (add key data left) k  d right
      else
        bal left k d (add key data right)

  let rec find : type a. a Key.t -> map -> a Data.t option = fun key -> function
    | Empty -> None
    | Node (left, k, d, right, _) ->
      match Key.eq_type key k with
      | Some Eq -> Some d
      | None -> find key (if Key.compare key k <= 0 then left else right)
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

  val eq_type : 'a k -> 'b k -> ('a, 'b) eq option

  module MkVector(D:sig type ('a,'b) t end)
    : Vector_hetero.S1 with
                         type 'a key = 'a k and type ('a,'b) data = ('a,'b) D.t

  module Vector  : Vector_hetero.R1 with type 'a key = 'a k
  module VectorH : Vector_hetero.T1 with type 'a key = 'a k

  module MkMap (Data : sig type 'a t end) : Map with type 'a key := 'a k
                                                 and type 'a data := 'a Data.t
end

module Str = struct
  type t = String.t
  let hash    = (Hashtbl.hash : string -> int)
  let equal   = ((=) : string -> string -> bool)
end

module HStr = Hashtbl.Make (Str)

let find_new_name used_names s =
  let rec aux used_names  s n =
    let sid = s ^ (string_of_int n) in
    if HStr.mem used_names sid then
      aux used_names s (n+1)
    else sid, (n+1)
  in
  try
    let n = HStr.find used_names s in
    let s', n = aux used_names s n in
    HStr.replace used_names s n;
    HStr.add     used_names s' 2;
    s'
  with Not_found ->
    HStr.add     used_names s 2;
    s

let incr_size new_size names =
  let capacity = Array.length !names in
  if capacity < new_size then
    let new_capacity = max (capacity * 2) new_size in
    let new_names = Array.make new_capacity "" in
    Array.blit !names 0 new_names 0 capacity;
    names := new_names

let register s i names used_names =
  let s = find_new_name used_names s in
  incr_size (i+1) names;
  !names.(i) <- s;


module Make (X : sig end) : S = struct
  type 'a k = int

  let names = ref (Array.make 100 "")
  let used_names = HStr.create 100

  let c = ref (-1)
  let create_key s =
    incr c;
    let i = !c in
    register s i names used_names;
    i

  let equal (x : int) y = x = y
  let eq_type : type a b. a k -> b k -> (a,b) eq option = fun a b ->
    if equal a b
    then Some ((Obj.magic (Eq : (a,a) eq)) : (a,b) eq)
    else None


  let compare (x : int) (y : int)  = Pervasives.compare x y
  let hash x = x
  let tag x = x

  let print fmt x =
    Format.pp_print_char fmt '@';
    Format.pp_print_string fmt !names.(x)

  let iter f =
    for i = 0 to !c do
      f i
    done

  let hint_size () = !c + 1

  module MkVector(D:sig type ('a,'b) t end) =
    Vector_hetero.Make1(struct type 'a t = 'a k end)(D)
  module Vector =
    Vector_hetero.RMake1(struct type 'a t = 'a k end)
  module VectorH =
    Vector_hetero.TMake1(struct type 'a t = 'a k end)

  module MkMap (Data : sig type 'a t end)
    = MkMap
      (struct type 'a t = 'a k let eq_type = eq_type let compare = compare end)
      (Data)
end
