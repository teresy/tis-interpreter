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

(** Print message and exits *)
val error: ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a
val bug: ('a, Format.formatter, unit, unit, unit, 'b) format6 -> 'a

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Type to represent some specification of the elements 
 * to add to the filesystem. *)
type fd

(** local_stat = treu means that the stat info comes from the local filesystem.
 * Otherwise default values frol the config file are used. *)
val virtual_from_local: local_stat:bool -> string -> string -> fd
val virtual_dir: string -> fd
val virtual_file: string -> fd
val virtual_generic_file: string -> size:int -> min:int -> max:int -> fd

type generic_file = private { gc_size: int; gc_min:int; gc_max:int}

type file_source = private SrcNone
                 | SrcLocal of string * bool (** bool is local_stat *)
                 | SrcGenericFile of generic_file

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** To represent inodes in the filesystem *)
module Inode : sig
  type t

  (** full name of the inode in the filesystem *)
  val c_name: t -> string

  (** number of the inode*)
  val num: t -> int

  (** if None, default values from config file are used *)
  val stat: t -> Unix.stats option

  (** same than stat st_size field, but needed when stat = None *)
  val st_size: t -> int option

  (* does the inode holds a regular file *)
  val is_file: t -> bool

  (* does the inode holds a directory *)
  val is_dir: t -> bool

  (** name of the local file to generate virtual file content.
   * Fail is the inode doesn't hold a file. *)
  val file_source: t -> file_source
end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

type filesystem

val fs_create: fd list -> filesystem
val fs_fold: ('a -> string -> Inode.t -> Inode.t list -> 'a) ->
  'a -> filesystem -> 'a
val fs_print: Format.formatter -> filesystem -> unit
val fs_next_inode_num: filesystem -> int

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
