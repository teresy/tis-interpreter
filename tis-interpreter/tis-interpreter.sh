#! /bin/sh

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

if [ -z "${TIS_INTERPRETER_USE_FRAMA_C+x}" ]
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

local builtins="\
  -val-builtin memcmp:tis_memcmp \
  -val-builtin memcpy:tis_memcpy \
  -val-builtin memset:tis_memset \
  -val-builtin memmove:tis_memmove \
  -val-builtin malloc:Frama_C_alloc_size \
  -val-builtin realloc:tis_realloc \
  -val-builtin free:Frama_C_free \
  -val-builtin strcmp:tis_strcmp \
  -val-builtin strlen:tis_strlen \
  -val-builtin strnlen:tis_strnlen \
  -val-builtin printf:tis_printf \
  -val-builtin sprintf:tis_sprintf \
  -val-builtin snprintf:tis_snprintf \
  -val-builtin strncmp:tis_strncmp \
  -val-builtin fprintf:tis_fprintf \
  -val-builtin strchr:tis_strchr \
  -val-builtin asprintf:tis_asprintf_interpreter \
  -val-builtin sscanf:tis_sscanf \
"

local options_interpreter_only="\
  -val-interpreter-mode \
  -val-stop-at-nth-alarm 1 \
  -obviously-terminates \
  -val-clone-on-recursive-calls"

local options_gui_only="-server -slevel 10000000"

local options="\
  -val \
  -unspecified-access \
  -val-malloc-plevel 10000 \
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
local compiler_opts="-C -E -isystem $TIS_PATH/share/frama-c/libc -dD -DTIS_INTERPRETER"

local others=""

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

        *)
            others="$others $1"
    esac
    shift
done

local final_compiler="$compiler $compiler_opts"

if [ "Q$preprocess_only" = "Q1" ];
then
    local SPECIAL_CONF="-D__FC_MACHDEP_X86_64"
    for file in $others;
    do
        case "$file" in
            -*);;
            *.ci) $final_compiler $SPECIAL_CONF ${file%.ci}.c > $file;;
            *.c)  $final_compiler $SPECIAL_CONF $file > ${file%.c}.ci;;
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
    
    $frama_c_binary -cpp-command="$final_compiler" \
                          $options $builtins $common_files \
                          $fc_runtime $others
fi

}

__tis_interpreter "$@"
