(* ocamlopt unix.cmxa translate.ml -o translate *)

let buffer = Bytes.create 1
let count  = ref 0

let rec aux () =
  match Unix.(read stdin buffer 0 1) with
  | 0 -> ()
  | 1 ->
    Printf.printf "%3d, " (Char.code (Bytes.get buffer 0));
    if !count = 14 then (Printf.printf "\n"; count := 0) else incr count;
    aux ()
  | _ -> assert false

let () =
  Printf.printf "#include <__fc_define_stat.h>\n";
  Printf.printf "#include \"mkfs_filesystem.h\"\n\n";
  Printf.printf "unsigned char fc_file_contents_input_array[] = {\n";
  aux ();
  Printf.printf "};\n\n\n";
  Printf.printf "
/* inode of 'input' */
struct stat fc_inode_input = {
  0,  /* ID of device containing file */
  1,  /* inode number */
  S_IFREG | S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH,  /* t_mode = kind + protection */
  1,  /* number of hard links */
  TIS_FILE_UID,  /* user ID of owner */
  TIS_FILE_GID,  /* group ID of owner */
  0,  /* device ID (if special file) */
  sizeof fc_file_contents_input_array,  /* total size, in bytes */
  0,  /* time of last access */
  0,  /* time of last modification */
  0,  /* time of last status change */
  1,  /* st_blksize field */
  1  /* st_blocks field */
};
"

