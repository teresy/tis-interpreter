This is tis-interpreter, an interpreter of C for detecting undefined behavior.

To compile, dependencies are version 4.02.3 of the OCaml compiler,
the Zarith library of OCaml bindings for GMP, and findlib. As of this writing
(April 2016), this means that the OCaml package from your Linux distribution
is likely to be too old. Your best bet is Opam, which is likely to be available
as a package in your distribution and can make the installation of recent OCaml
and OCaml dependencies a breeze.

Configure with:
```
./configure --prefix=`pwd`/tis-interpreter/tis-interpreter --disable-from_analysis --disable-gui --disable-impact --disable-inout --disable-metrics --disable-occurrence --disable-pdg --disable-postdominators --enable-rtegen --disable-scope --disable-slicing --disable-sparecode --enable-users --disable-aorai --disable-obfuscator --disable-report --disable-security_slicing --disable-wp --disable-wp-coq --disable-wp-why3 --disable-print_api --with-all-static
```

Then continue compilation:
```
make depend

make

make install
```

That last command should have populated the subdirectory
`tis-interpreter` with the binary and header files, so that this
directory now constitutes a self-contained binary tis-interpreter
package. This directory can be moved around, and the script
`tis-interpreter.sh` will look for support files wherever it has been
moved to.

If you are using Ubuntu trusty, then you can use the
[.travis.yml](https://github.com/TrustInSoft/tis-interpreter/blob/master/.travis.yml)
file as an explicit, step-by-step installation guide for all the necessary
dependencies.

[![Build Status](https://travis-ci.org/TrustInSoft/tis-interpreter.svg?branch=master)](https://travis-ci.org/TrustInSoft/tis-interpreter)
