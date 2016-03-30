#include "__tis_mkfs.h"
#include "mkfs_filesystem.h"

/* Contents for '.' and '..' */
struct dirent fc_dir_dot = {0, 0, 0, 0, {46, 0}};
struct dirent fc_dir_dot_dot = {0, 0, 0, 0, {46, 46, 0}};

/* inode of 'input' */
extern struct stat fc_inode_input;
extern unsigned char fc_file_contents_input_array[];

unsigned char * fc_file_contents_1 (void) {
  return fc_file_contents_input_array;
}
/* List of files */
struct __fc_fs_file __fc_fs_files[16] = {
  {"input", &fc_inode_input, &fc_file_contents_1},
};
int __fc_fs_files_nb = 1;
int __fc_fs_files_nb_max = 16;
/* List of directories */
struct __fc_fs_dir __fc_fs_dirs[1];
int __fc_fs_dirs_nb = 0;
int __fc_fs_dirs_nb_max = 0;
int __tis_mkfs_get_file (const char *path) {
  //@ loop pragma UNROLL 16;
  for (int i = 0; i < __fc_fs_files_nb; i++)
    if (__fc_fs_files[i].__fc_fullpath && strcmp(__fc_fs_files[i].__fc_fullpath, path) == 0)
      return i;
  return -1;
}
int __tis_mkfs_get_dir (const char *path) {
  //@ loop pragma UNROLL 0;
  for (int i = 0; i < __fc_fs_dirs_nb; i++)
    if (__fc_fs_dirs[i].__fc_fullpath && strcmp(__fc_fs_dirs[i].__fc_fullpath, path) == 0)
      return i;
  return -1;
}
uid_t __tis_uid = TIS_uid;
gid_t __tis_gid = TIS_gid;
uid_t __tis_euid = TIS_euid;
gid_t __tis_egid = TIS_egid;


int __tis_next_inode = 1;

