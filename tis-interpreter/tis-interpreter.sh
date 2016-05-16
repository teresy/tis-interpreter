#! /bin/bash

__error() {
echo "$@" >&2
}

__doc() {
cat <<EOF
$0 [opts]
script to launch tis-interpreter

Options:
    --cc "opt str"            add C compiler options (as "-Ifolder -Iother"...)
    --help                    show this help

Every other options are transmitted as-is to tis-interpreter.
EOF
}

__tis_interpreter() {

ROOT_PATH=`dirname $0`
TIS_PATH=$ROOT_PATH/tis-interpreter

local frama_c_binary="frama-c"

if [ -z "${TIS_INTERPRETER_USE_FRAMA_C}" ]
then
  # If TIS_INTERPRETER_USE_FRAMA_C variable is not set
  # then we use the local Frama-C installation.

  export FRAMAC_SHARE=$TIS_PATH/share/frama-c
  export FRAMAC_LIB=$TIS_PATH/lib/frama-c
  export FRAMAC_PLUGIN=$TIS_PATH/lib/frama-c/plugins
  export OCAMLFIND_CONF=/dev/null

  frama_c_binary="$TIS_PATH/bin/frama-c"
fi

local preprocess_only="0"
local gui="0"
local filesystem="0"

local builtins="\
  -val-builtin memcmp:tis_memcmp \
  -val-builtin memcpy:tis_memcpy \
  -val-builtin memmove:tis_memmove \
  -val-builtin wmemcpy:tis_wmemcpy \
  -val-builtin wmemmove:tis_wmemmove \
  -val-builtin memset:tis_memset \
  -val-builtin memchr:tis_memchr \
  -val-builtin malloc:Frama_C_alloc_size \
  -val-builtin realloc:tis_realloc \
  -val-builtin free:Frama_C_free \
  -val-builtin strcmp:tis_strcmp \
  -val-builtin wcscmp:tis_wcscmp \
  -val-builtin strncmp:tis_strncmp \
  -val-builtin wcsncmp:tis_wcsncmp \
  -val-builtin strcpy:tis_strcpy \
  -val-builtin wcscpy:tis_wcscpy \
  -val-builtin strlen:tis_strlen \
  -val-builtin wcslen:tis_wcslen \
  -val-builtin strcat:tis_strcat \
  -val-builtin wcscat:tis_wcscat \
  -val-builtin strnlen:tis_strnlen \
  -val-builtin wcsnlen:tis_wcsnlen \
  -val-builtin printf:tis_printf \
  -val-builtin wprintf:tis_wprintf \
  -val-builtin sprintf:tis_sprintf \
  -val-builtin asprintf:tis_asprintf_interpreter \
  -val-builtin snprintf:tis_snprintf \
  -val-builtin fprintf:tis_fprintf \
  -val-builtin strchr:tis_strchr \
  -val-builtin strtol:tis_strtol_interpreter \
  -val-builtin strtoul:tis_strtoul_interpreter \
  -val-builtin strtoll:tis_strtoll_interpreter \
  -val-builtin strtoull:tis_strtoull_interpreter \
  -val-builtin atoi:tis_atoi_interpreter \
  -val-builtin atol:tis_atol_interpreter \
  -val-builtin atoll:tis_atoll_interpreter \
  -val-builtin atoq:tis_atoll_interpreter \
  -val-builtin strtof:tis_strtof_interpreter \
  -val-builtin strtod:tis_strtod_interpreter \
  -val-builtin atof:tis_atof_interpreter \
  -val-builtin sscanf:tis_sscanf \
  -val-builtin scanf:tis_scanf \
  -val-builtin alloca:Frama_C_alloc_size \
  -val-builtin ceil:Frama_C_ceil \
  -val-builtin trunc:Frama_C_trunc \
  -val-builtin floor:Frama_C_floor \
  -val-builtin sqrt:Frama_C_sqrt \
"

local options_interpreter_only="\
  -val-interpreter-mode \
  -val-stop-at-nth-alarm 1 \
  -obviously-terminates \
  -val-clone-on-recursive-calls"

local options_gui_only="-server -slevel 10000000"

local options="\
  -val \
  -warn-decimal-float none \
  -unspecified-access \
  -val-warn-pointer-arithmetic-out-of-bounds \
  -val-malloc-plevel 1000000000 \
  -val-slevel-merge-after-loop=-@all \
  -no-val-print \
  -no-val-show-initial-state \
  -no-val-show-progress \
  -val-print-callstacks \
  -cpp-gnu-like \
  -machdep x86_64 \
  -val-warn-harmless-function-pointers \
  -val-show-slevel 1000000000"

local fc_runtime=$TIS_PATH/share/frama-c/libc/fc_runtime.c

local common_files="\
  $ROOT_PATH/common_helpers/common_missing.c \
  $TIS_PATH/share/frama-c/libc/tis_stdlib.c \
  $ROOT_PATH/common_helpers/common_env.c \
  $ROOT_PATH/common_helpers/common_resource.c \
  $ROOT_PATH/common_helpers/common_time.c"

local compiler=cc
local compiler_opts="-C -E -isystem $TIS_PATH/share/frama-c/libc -I $ROOT_PATH/filesystem -dD -DTIS_INTERPRETER -D__TIS_USER_FPUTS -D__TIS_USER_PUTS  -D__FC_MACHDEP_X86_64"

declare -a others

while [ ! "X$1" = "X" ];
do
    case $1 in

        --cc)
            compiler_opts="$compiler_opts $2";
            shift;;

        --help)
            __doc
            exit 1;;

        --preprocess-only)
            preprocess_only="1";;

        --gui)
            gui="1";;

        --fs)
            filesystem="1";;
        
        *)
            others=("${others[@]}" "$1")
    esac
    shift
done

local final_compiler="$compiler $compiler_opts"

if [ "Q$filesystem" = "Q1" ];
then
    others=("${others[@]}" "$ROOT_PATH/filesystem/__tis_mkfs.c")
fi    

if [ "Q$preprocess_only" = "Q1" ];
then
    for file in "${others[@]}";
    do
        case "$file" in
            -*);;
            *.ci) $final_compiler ${file%.ci}.c > $file;;
            *.c)  $final_compiler $file > ${file%.c}.ci;;
            *)    echo Unknown file.
        esac
    done
else
    if [ "Q$gui" = "Q1" ];
    then
            options="$options $options_gui_only"
    else
            options="$options $options_interpreter_only"
    fi

    exec $frama_c_binary -cpp-command="$final_compiler" \
                          $options $builtins $common_files \
                          $fc_runtime "${others[@]}";
fi

}

__tis_interpreter "$@"
