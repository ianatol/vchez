# vchez
## Coq
### Overview
We provide an implementation of a subset of the R6RS Formal semantics `http://www.r6rs.org/final/html/r6rs/r6rs-Z-H-15.html#node_chap_A`

### How to run
First, install the Metalib library: https://github.com/plclub/metalib

Then, create a makefile:
`coq_makefile -f _CoqProject *.v -o Makefile`

Finally, call `make` to build the project

## Racket/Scheme
### Overview
We provide a testing framework for showing that the `convert-assignments` pass is correct for given programs

### How to run
Execute `test-transform.rkt` to run the test suite

To test a specific program, call `test-ca` on it to test for one step,
or `full-test-ca` to test for 10 steps or until the program terminates