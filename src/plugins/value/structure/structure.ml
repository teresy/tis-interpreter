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

module type Shape = sig
  include Key.S

  type 'a structure =
    | Void : 'a structure
    | Leaf : 'a k -> 'a structure
    | Node : 'a structure * 'b structure -> ('a * 'b) structure
end

module type Internal = sig
  type t
  type 'a structure
  val structure : t structure
end

module type External = sig
  type t
  type 'a key
  val mem : 'a key -> bool
  val get : 'a key -> (t -> 'a) option
  val set : 'a key -> 'a -> t -> t
end

module MkTree
    (Data : sig type 'a t end)
= struct

  type 'a tree =
    | SEmpty
    | SLeaf of 'a Data.t
    | SNode of 'a tree * 'a tree

  let empty = SEmpty
  let singleton data = SLeaf data
  let merge left right = match left, right with
    | SEmpty, _ -> right
    | _, SEmpty -> left
    | _, _ -> SNode (left, right)

  let rec map f = function
    | SEmpty -> SEmpty
    | SLeaf data -> SLeaf (f data)
    | SNode (l, r) -> SNode (map f l, map f r)

  let rec fold f tree acc = match tree with
    | SEmpty -> acc
    | SLeaf data -> f data acc
    | SNode (l, r) -> fold f r (fold f l acc)
end


module Open
    (Shape : Shape)
    (M : sig type t val structure : t Shape.structure end)
= struct

  open Shape

  let rec mem : type a. 'v k -> a structure -> bool = fun key -> function
    | Void -> false
    | Leaf k -> Shape.equal key k
    | Node (left, right) -> mem key left || mem key right

  let mem key = mem key M.structure

  type ('a, 'b) get = 'b Shape.k * ('a -> 'b)

  type 'a getter = Get : ('a, 'b) get -> 'a getter

  module GTree = MkTree (struct type 'a t = 'a getter end)

  let lift_get f (Get (key, get)) = Get (key, fun t -> get (f t))

  let rec compute_getters : type a. a structure -> a GTree.tree = function
    | Void -> GTree.empty
    | Leaf key ->  GTree.singleton (Get (key, fun (t : a) -> t))
    | Node (left, right) ->
      let l = compute_getters left and r = compute_getters right in
      let l = GTree.map (lift_get fst) l and r = GTree.map (lift_get snd) r in
      GTree.merge l r


  type ('a, 'b) set = 'b Shape.k * ('b -> 'a -> 'a)

  type 'a setter = Set : ('a, 'b) set -> 'a setter

  module STree = MkTree (struct type 'a t = 'a setter end)

  let lift_set f (Set (key, set)) = Set (key, fun v b -> f (fun a -> set v a) b)

  let rec compute_setters : type a. a structure -> a STree.tree = function
    | Void -> STree.empty
    | Leaf key -> STree.singleton (Set (key, fun v _t -> v))
    | Node (left, right) ->
      let l = compute_setters left and r = compute_setters right in
      let l = STree.map (lift_set (fun set (l, r) -> set l, r)) l
      and r = STree.map (lift_set (fun set (l, r) -> l, set r)) r in
      STree.merge l r

  (* Store accessors using the heterogeneous vectors of Popup. *)

(*
  module Getters = Key.MkVector (struct type ('a, 'b) t = M.t -> 'a end)

  let getters : unit Getters.t = Getters.create 4

  let () =
    let list = compute_getters M.structure in
    let process (Get (key, get)) () =
      Getters.inc_size key getters;
      Getters.set getters key get
    in
    GTree.fold process list ()

  let get key =
    match Getters.get_opt getters key with
    | None -> fun _ -> None
    | Some g -> fun x -> Some (g x)


  module Setters = Key.MkVector (struct type ('a, 'b) t = M.t -> 'a -> M.t end)

  let setters : unit Setters.t = Setters.create 4

  let () =
    let list = compute_setters M.structure in
    let process (Set (key, set)) () =
      Setters.inc_size key setters;
      Setters.set setters key set
    in
    STree.fold process list ()

  let set key = Setters.get setters key
*)

  (* Store the accessors using maps of keys. *)

  module Getters = Shape.MkMap (struct type 'a t = M.t -> 'a end)

  let getters =
    GTree.fold
      (fun (Get (k, d)) acc -> Getters.add k d acc)
      (compute_getters M.structure)
      Getters.empty

  let get key = Getters.find key getters


  module Setters = Shape.MkMap (struct type 'a t = 'a -> M.t -> M.t end)

  let setters =
    STree.fold
      (fun (Set (k, d)) acc -> Setters.add k d acc)
      (compute_setters M.structure)
      Setters.empty

  let set key = match Setters.find key setters with
    | None -> fun _ t -> t
    | Some s -> s

end


module Make_Key (S : sig end) = struct
  include Key.Make (S)

  type 'a structure =
    | Void : 'a structure
    | Leaf : 'a k -> 'a structure
    | Node : 'a structure * 'b structure -> ('a * 'b) structure
end


module Key_Value = Make_Key (struct end)
module Key_Location = Make_Key (struct end)
module Key_Domain = Make_Key (struct end)
