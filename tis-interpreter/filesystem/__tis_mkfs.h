/**************************************************************************/
/*                                                                        */
/*  This file is part of tis-interpreter.                                 */
/*  Copyright (C) 2016 TrustInSoft                                        */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  General Public License as published by the Free Software              */
/*  Foundation, version 2.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU General Public License version 2 for more details.                */
/*  (enclosed in the file licences/GPLv2).                                */
/*                                                                        */
/**************************************************************************/

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/socket.h>

#include <__fc_builtin.h>

//===============================================================================
// Constants variables to be used in annotations without preprocessing.
//-------------------------------------------------------------------------------

const int __tis_FOPEN_MAX = FOPEN_MAX;
const int __tis_R_OK = R_OK;
const int __tis_W_OK = W_OK;
const int __tis_X_OK = X_OK;
const int __tis_F_OK = F_OK;

const int __tis_O_RDWR = O_RDWR;
const int __tis_O_WRONLY = O_WRONLY;
const int __tis_O_RDONLY = O_RDONLY;
const int __tis_O_CREAT = O_CREAT;

//===============================================================================
// Exported types and API
//-------------------------------------------------------------------------------
// File descriptor management.
// The local information is only to store the kind of the opened object
// to be able to find its information in the appropriate array
// (see __tis_fd_info description below).
//-------------------------------------------------------------------------------
// TODO: at the moment, the file descriptor is also used as index
// in the different arrays, but it makes it impossible to have the same FILE for
// two different fd (see dup). __tis_fd_info should better store an index
// to find the information in the appropriate array.
//-------------------------------------------------------------------------------
struct __tis_fd_info {
  int __tis_fd_kind; // S_IFREG (file): information in __fc_fopen
                     // S_IFDIR (directory): information in __fc_opendir
                     // S_IFCHR (stdin, stdout, stderr):
                     //                      information in __fc_fopen
                     // S_IFIFO (pipe): information in __fc_fopen
                     // S_IFSOCK (socket): information in __tis_fd_socket
                     // 0 when the file descriptor is not used.
};

// array of opended file descriptors.
extern struct __tis_fd_info __tis_file_desc[FOPEN_MAX];

//-------------------------------------------------------------------------------
// About sockets:
//-------------------------------------------------------------------------------
struct __tis_socket {
  int __tis_sock_id;
  struct sockaddr *__tis_sock_addr;
  socklen_t __tis_sock_addrlen;
  int __tis_sock_domain;
  int __tis_sock_type;
  int __tis_sock_protocol;
  struct stat __tis_sock_stat;
};
extern struct __tis_socket __tis_fd_socket[FOPEN_MAX];

//-------------------------------------------------------------------------------
// Useful functions for users implementations:
// all of them return 0 if ok or set errno and return -1 otherwise.
//-------------------------------------------------------------------------------
int __tis_check_fd_ok (int fd);

// file also includes S_IFCHR and S_IFIFO.
int __tis_check_fd_file_ok (int fd);
int __tis_check_fd_file_ok_for_reading (int fd);
int __tis_check_fd_file_ok_for_writing (int fd);

int __tis_check_fd_dir_ok (int fd);
int __tis_check_fd_socket_ok (int fd);

int __tis_seekable (int fd);

//===============================================================================
// Declaration from generated file.
//-------------------------------------------------------------------------------

struct __fc_fs_dir {
  char *__fc_fullpath;
  struct stat * __fc_stat;
  struct dirent ** __fc_dir_entries;
};

extern int __tis_mkfs_get_file(const char *path);
extern int __tis_mkfs_get_dir(const char *path);

extern struct __fc_fs_file __fc_fs_files[];
extern int __fc_fs_files_nb, __fc_fs_files_nb_max;

extern struct __fc_fs_dir __fc_fs_dirs[];
extern int __fc_fs_dirs_nb, __fc_fs_dirs_nb_max;

extern uid_t __tis_uid;
extern uid_t __tis_gid;
extern uid_t __tis_euid;
extern uid_t __tis_egid;

extern int __tis_next_inode;
extern int __tis_default_inode_size;

//===============================================================================
// Missing from Frama-C
//-------------------------------------------------------------------------------

// mkstemp should be declared in stdlib.h (POSIX)
int mkstemp(char *template);

// link should be declared in unistd.h
// TODO: implement link, which requires a bit of work: we need to stop
// storing the file name in __fc_fs_file, since __fc_fs_file is really
// an inode. the file name(s) need to move into directory entries.
int link(const char *oldpath, const char *newpath);

int fflush(FILE *stream);

void *mmap(void *addr, size_t length, int prot, int flags,
	   int fd, off_t offset);
int munmap(void *addr, size_t length);

#ifndef __TIS_MKFS_BLKSIZE
#define __TIS_MKFS_BLKSIZE 512
#endif

#ifndef __TIS_MKFS_ST_DEV
#define __TIS_MKFS_ST_DEV 88
#endif

//===============================================================================
