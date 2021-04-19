# vchez

## How to run
First, install the TLC library:

`opam repo add coq-released http://coq.inria.fr/opam/released`

`opam install -j4 coq-tlc`

Then, create a makefile:

`coq_makefile -f _CoqProject *.v -o Makefile`

Finally, call `make` to build the project
