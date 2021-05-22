# vchez
## Coq
### Overview
We provide an implementation of a subset of the [R6RS Formal semantics](http://www.r6rs.org/final/html/r6rs/r6rs-Z-H-15.html).

### How to run
First, install [Coq](https://coq.inria.fr/download).
I used Coq 8.10 - newer versions are likely to work but untested.
I recommend using opam for installation, as it is quite simple (and required for the next step).

Then, install the [Metalib library](https://github.com/plclub/metalib) in coq/metalib
(Note: You may have to change the Coq version in metalib's makefile to correspond to the version of Coq you are using)

Next, create a makefile: `coq_makefile -f _CoqProject *.v -o Makefile`

Finally, call `make` to build the project

You can step through some of the examples in **Examples.v** to see how the semantic model works

## Racket/Scheme
### Overview
We provide a testing framework for showing that the _convert-assignments_ pass is correct for given programs

### How to run
Install Racket. I recommend using the [DrRacket IDE](https://download.racket-lang.org/).
I used Racket 8.0 when writing this framework.

Run **test-transform.rkt** to run the test suite

To test a specific program, call `test-ca` on it to test for one step,
or `full-test-ca` to test for 10 steps or until the program terminates

You can modify the definition of `full-test-ca` to change the step limit.
