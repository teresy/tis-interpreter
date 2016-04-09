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

let error fmt =
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter ("ERROR: "^^fmt^^"@.")

let bug fmt =
  Format.kfprintf (fun _ -> assert false)
    Format.err_formatter ("ERROR: "^^fmt^^"@.")

(*=============================================================================*)

type generic_file = { gc_size: int; gc_min:int; gc_max:int}
type file_source =
  | SrcNone
  | SrcLocal of string * bool (** bool is for local_stat *)
  | SrcGenericFile of generic_file

(* type socket_descr = { port: int; data: file_descr } *)

type inode_info = { si_size: int option; si_kind: Unix.file_kind }
type stat_info = Sstat of Unix.stats | Sinfo of inode_info

module Request = struct

  type t =
    | File of string * file_source
    (* | Socket of socket_descr *)
    | Dir of string * (string * bool) option

  let mk_dir name src =
    (* Format.printf "Request.mk_dir: %s@." name; *)
    Dir (name, src)

  let mk_file name src =
    (* Format.printf "Request.mk_file: %s@." name; *)
    File (name, src)

  let is_dir fd = match fd with File _ -> false | Dir _ -> true
  let is_file fd = match fd with File _ -> true | Dir _ -> false

  let c_name fd = match fd with
  | File (name, _) -> name
  | Dir (name, _) -> name

  let file_content fd = match fd with
  | File (_, src) -> Some src
  | Dir (_, _) -> None

  let src_name fd = match fd with
  | File (_, SrcLocal (src_name, _)) -> Some src_name
  | File (_, (SrcNone | SrcGenericFile _)) -> None
  | Dir (_, Some (src_name, _)) -> Some src_name
  | Dir (_, None) -> None

  let use_local_stat fd = match fd with
  | File (_, SrcLocal (_src_name, true))
  | Dir (_, Some (_src_name, true)) -> true
  | File (_, (SrcNone | SrcGenericFile _ | SrcLocal _)) -> false
  | Dir _ -> false

  let mk_stat fd ino = match fd with
    | Dir (_, Some (src_name, true))
    | File (_, SrcLocal (src_name, true)) ->
      let st = Unix.stat src_name in
      Sstat { st with Unix.st_ino = ino }
    | Dir _ -> Sinfo { si_size = Some 0; si_kind = Unix.S_DIR }
    | File (_, SrcGenericFile { gc_size; _ }) ->
      Sinfo { si_size = Some gc_size; si_kind = Unix.S_REG }
    | File (_, (SrcNone | SrcLocal _)) ->
        Sinfo { si_size = None; si_kind = Unix.S_REG }
end

let virtual_from_local ~local_stat c_name src_name =
  try
    if Sys.is_directory src_name
    then Request.mk_dir c_name (Some (src_name, local_stat))
    else Request.mk_file c_name (SrcLocal (src_name, local_stat))
  with Sys_error msg -> error "bad local element: %s@." msg

let virtual_dir c_name = Request.mk_dir c_name None

let virtual_file c_name = Request.mk_file c_name SrcNone

let virtual_generic_file c_name ~size ~min ~max =
  let src = SrcGenericFile { gc_size=size; gc_min=min; gc_max=max} in
  Request.mk_file c_name src

module Inode = struct

  type t =
    { i_node: int;
      i_name: string; (* to be modified to handle links one day *)
      i_stat: stat_info;
      i_source : file_source option; (* only for files *)
    }

  let stat inode = match inode.i_stat with
  | Sstat st -> Some st
  | Sinfo _ -> None

  let st_size inode = match inode.i_stat with
  | Sstat st -> Some st.Unix.st_size
  | Sinfo si -> si.si_size

  let st_kind inode = match inode.i_stat with
  | Sstat st -> st.Unix.st_kind
  | Sinfo si -> si.si_kind

  let c_name inode = inode.i_name

  let file_source inode = match inode.i_source with
    | None -> assert false
    | Some src -> src

  let num inode = inode.i_node

  let is_file inode = st_kind inode = Unix.S_REG
  let is_dir inode = st_kind inode = Unix.S_DIR

  let counter = ref 0
  let tbl = Hashtbl.create 10

  let find c_name = Hashtbl.find tbl c_name

  (*
  let pp fmt inode =
    Format.fprintf fmt "%d: %s %s"
    inode.i_node (if is_file inode then "file" else "directory") inode.i_name
    *)

  let make fd =
    let i_name = Request.c_name fd in
    try find i_name
    with Not_found ->
      incr counter;
      let i_source = Request.file_content fd in
      let i_stat = Request.mk_stat fd !counter in
      let inode = { i_node = !counter; i_name; i_stat; i_source; } in
      (* Format.printf "Inode.make -> %a@." pp inode; *)
      Hashtbl.add tbl i_name inode;
      inode
end

module Tree = struct

  (** The name here is the local name, without path.
   * The list of kids must be empty for files.
   *)
  type t = string * Inode.t * t list

  let is_dir (_name, inode, _) = Inode.is_dir inode
  let is_file (_name, inode, _) = Inode.is_file inode

  let mk name inode kids =
    let t = (name, inode, kids) in assert (kids = [] || is_dir t); t

  let mk_new name fd kids =
    let inode = Inode.make fd in mk name inode kids

  let rec fold f acc fs = match fs with [] -> acc
      | (name, inode, kids) :: tl ->
          let acc = fold f acc kids in
          let acc = f acc name inode (List.map (fun (_,inode,_) -> inode) kids)
          in fold f acc tl

  let pp fmt fs =
    let rec pp_level fmt x =
      match x with
      | [] -> ()
      | false::[] ->   Format.fprintf fmt "├── "
      | true::[] ->    Format.fprintf fmt "└── "
      | false :: tl -> Format.fprintf fmt "│   %a" pp_level tl
      | true :: tl ->  Format.fprintf fmt "    %a" pp_level tl
    in
    let rec pp_tree fmt (n, e) = match e with
    | (name, _, l) ->
        let name = if is_dir e && name <> "/" then name ^ "/" else name in
        Format.fprintf fmt "%a%s@.%a" pp_level n name
          pp_list_tree (n, l)
    and pp_list_tree fmt (n, l) = match l with
      | [] -> ()
      | x::[] -> Format.fprintf fmt "%a" pp_tree (n @ [true], x)
      | x::tl ->
          Format.fprintf fmt "%a%a" pp_tree (n @ [false], x)
                                    pp_list_tree (n, tl)
    in Format.fprintf fmt "FileSystem=@.%a@."
      (fun fmt ->  List.iter (fun x -> pp_tree fmt ([], x))) fs

  let rec add_to_subtrees st_c_name subtrees rel_c_path_list fd =
    match rel_c_path_list with
    | [] -> bug "empty rel_c_path_list"
    | name :: path -> (* find or add dir at this level and add path in it *)
        (* Format.printf "add_to_subtrees: '%s' in '%s' in %a@."
        name st_c_name pp subtrees; *)
        let rec add l = match l with
          | [] ->
              if path = [] then (* this is it: create new element here *)
                (mk_new name fd []) :: []
              else (* need to create indermediate directory *)
                begin
                let dir_name = Filename.concat st_c_name name in
                let dir_fd = virtual_dir dir_name in
                let elems = add_to_subtrees dir_name [] path fd in
                let e = mk_new name dir_fd elems in
                e :: []
                end
          | ((id, inode, elems) as t) :: stl when id = name ->
              (* this sub-tree *)
            if is_dir t then
              begin
                if path = [] then
                  if Request.is_dir fd then
                    (* directory already exists: keep quiet and do nothing *)
                    t :: stl
                  else if Request.is_file fd then
                    error "cannot add '%s' in '%s': directory already exists."
                      name st_c_name
                  else bug ("neither file nor directory ?")
                else
                  let dir_name = Filename.concat st_c_name name in
                  let elems = add_to_subtrees dir_name elems path fd
                  in (id, inode, elems) :: stl
              end
            else if is_file t then
              error "cannot add '%s' in '%s': file already exists"
                name st_c_name
            else bug "'%s' in '%s' neither file nor dir ?" id st_c_name
          | st :: stl -> (* not this sub-tree: keep going *) st :: (add stl)
        in add subtrees

  let mk_path c_name =
    let c_path_list = Str.split (Str.regexp_string "/") c_name in
      if c_name.[0] = '/' then "/"::c_path_list else c_path_list

      (* error "Invalid file %S: expecting a file or a directory." src_name *)

  let rec add fs fd =
    let c_name = Request.c_name fd in
    (*Format.printf "add: %s '%s'@."
    (if Request.is_file fd then "file" else "dir") c_name; *)
    let c_path_list = mk_path c_name in
    let fs = add_to_subtrees "" fs c_path_list fd in
    match Request.src_name fd with
    | Some src_name when Request.is_dir fd ->
        let dirents = Sys.readdir src_name in
        let () = Array.sort String.compare dirents in
        let add_dirent fs name =
          let c_name = Filename.concat c_name name in
          let src_name = Filename.concat src_name name in
          let local_stat = Request.use_local_stat fd in
          let fd = virtual_from_local ~local_stat c_name src_name in
          add fs fd
        in Array.fold_left add_dirent fs dirents
    | Some _ | None -> (* file or no source = nothing more to do *) fs
end

type fd = Request.t
type filesystem = int * Tree.t list

let fs_next_inode_num (n, _fs) = n
let fs_fold f acc (_, fs) = Tree.fold f acc fs
let fs_print fmt (_, fs) = Tree.pp fmt fs

let fs_create lst = !Inode.counter, List.fold_left Tree.add [] lst

