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

let out_file_name = ref "mkfs_filesystem.c"
let separator = ref ":"
let elements = ref []
let print = ref false
let nb_max_files = ref None
let nb_max_dirs = ref None

let parse_max var n =
  let n =
    try int_of_string n
    with Failure "int_of_string" ->
      Mkfs_build.error "the max argument must be an int. Found '%s'." n
  in var := Some n

let parse_file s = 
  let fd = Mkfs_build.virtual_file s in
  elements := fd :: !elements

let parse_dir s =
  let fd = Mkfs_build.virtual_dir s in
  elements := fd :: !elements

let parse_local s =
  match Str.split (Str.regexp_string !separator) s with
  | [c_name; src_name] ->
      let fd = 
        Mkfs_build.virtual_from_local ~local_stat:true c_name src_name
      in
      elements := fd :: !elements
  | _ ->
    Mkfs_build.error
      "Invalid filename mapping %S: expecting 'virtual_name%slocal_name'" 
      s !separator


let cmdline = [
  "-local", Arg.String parse_local,
    "<c_name:local_name> add an element <c_name> in the virtual filesystem\n\
\    that is similar to the <local_name> element.\n\
\    - if <local_name> is a file, <c_name> has the same content;\n\
\    - if <local_name> is a directory, <c_name> has recursively\n\
\      the same tree structure with the same files." ;
  "-add-file", Arg.String parse_file,
    "<c_name> add a file named <c_name> in the filesystem.\n\
\    The name may include a path to specify where to put it,\n\
\    and in that case, the intermediate directories are created.\n\
\    The content of the file is unknown." ;
  "-add-dir", Arg.String parse_dir,
    "<c_name> add a directory named <c_name> in the filesystem.\n\
\    The name may include a path to specify where to put it.\n\
\    It is empty except is the -add-file option is also used." ;
  "-nb-max-files", Arg.String (parse_max nb_max_files),
   "<n> if the analyzed program creates new files, the filesystem array\n\
\   must be bigger than the initial number of files.\n\
\   This option sets the maximum number of files in the whole filesystem.";
  "-nb-max-dirs", Arg.String (parse_max nb_max_dirs),
  "<n> is similar to the -nb-max-files option, but for directories.";
  "-sep",Arg.Set_string separator,
    "<separator> to change the separator in options (default: '"^ !separator ^"')";
  "-o",Arg.Set_string out_file_name,
    "<output_filename> (default: "^ !out_file_name ^")";

  "-print", Arg.Set print, "print the generated filesystem to stdout";
]

let () =
  Arg.parse cmdline
    (fun s -> raise (Arg.Bad s))
    "Generate a virtual filesystem for TrustInSoft analyzer.\n\
    More information in $(tis-analyzer -print-share-path)/../tis/manuals/tis-mkfs.pdf.\n\n\
    Options are:";
  let fs = Mkfs_build.fs_create !elements in
  if !print then Format.printf "%a" Mkfs_build.fs_print fs;
  Mkfs_print.export ~nb_max_files:!nb_max_files ~nb_max_dirs:!nb_max_dirs
    !out_file_name fs

