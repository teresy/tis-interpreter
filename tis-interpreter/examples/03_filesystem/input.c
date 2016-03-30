#include <__fc_define_stat.h>
#include "mkfs_filesystem.h"

unsigned char fc_file_contents_input_array[] = {
255, 216, 255, 224,   0,  16,  74,  70,  73,  70,   0,   1,   1,   1,   0, 
 96,   0,  96,   0,   0, 255, 219,   0,  67,   0,   2,   1,   1,   1,   1, 
  1,   2,   1,   1,   1,   2,   2,   2,   2,   2,   4,   3,   2,   2,   2, 
  2,   5,   4,   4,   3,   4,   6,   5,   6,   6,   6,   5,   6,   6,   6, 
  7,   9,   8,   6,   7,   9,   7,   6,   6,   8,  11,   8,   9,  10,  10, 
 10,  10,  10,   6,   8,  11,  12,  11,  10,  12,   9,  10,  10,  10, 255, 
219,   0,  35,   1,   2,   2,  10,  10,  10,  10,  10,  10,  10,  10,  10, 
 10,  10,  10,   0,   0,   0,   0,   0,   0,   0,   9,   1,   8,   6,   7, 
 10,   5,   4,   3,   2, 255, 196,   0,  65,  10,  19,  81,  20,  34,  97, 
113, 129,  21,  50, 145, };



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
