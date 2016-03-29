This is tis-interpreter, an interpreter of C for detecting undefined behavior.

To compile, dependencies are a recent version of the OCaml compiler,
the Zarith library of OCaml bindings for GMP, and findlib.

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
