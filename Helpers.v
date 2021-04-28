From Coq Require Import Strings.String.

Inductive OptionE (X : Type) : Type :=
| SomeE (x : X)
| NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

Notation "' p <- e1 ;; e2"
 := (match e1 with
     | SomeE p => e2
     | NoneE err => NoneE err
     end)
 (right associativity, p pattern, at level 60, e1 at next level).

