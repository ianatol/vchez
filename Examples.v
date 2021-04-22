From vchez Require Export Definitions.
From vchez Require Export Pass.
From Coq Require Import List.
Import ListNotations.

Example ca_1 : forall x,
  ca (trm_fvar x) = SomeE (trm_fvar x).
Proof. reflexivity. Qed.

Example ca_2 : forall v1 v2,
  ca (trm_let v1 [trm_let v2 [trm_bvar 0]]) =
  SomeE (trm_let v1 [trm_let v2 [trm_bvar 0]]).
Proof. reflexivity. Qed.

Example ca_3 : forall v1 v2,
  ca (trm_let v1 [trm_let v2 [trm_bvar 0; trm_bvar 1]]) =
  SomeE (trm_let v1 [trm_let v2 [trm_bvar 0; trm_bvar 1]]).
Proof. reflexivity. Qed.

Example ca_4 : forall v1,
  ca (trm_let v1 [trm_bvar 0]) =
  SomeE (trm_let v1 [trm_bvar 0]).
Proof. reflexivity. Qed.

Example ca_5 :
  ca (trm_let trm_false
       [trm_set (trm_bvar 0) trm_true]) =
  SomeE (trm_let trm_false
          [trm_let (trm_cons (trm_bvar 0) (trm_null)) 
            [trm_setcar (trm_bvar 0) trm_true]]).
Proof. reflexivity. Qed.


(*These examples show the algorithm for finding set! that refer to a variable bound by a let*)
Example set1 :
  handle_sets (trm_set (trm_bvar 0) (trm_null)) =
              SomeE (trm_setcar (trm_bvar 0) trm_null).
Proof.
  reflexivity. Qed.

