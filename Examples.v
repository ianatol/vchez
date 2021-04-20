From vchez Require Export Definitions.
From vchez Require Export Pass.

Example set1 :
  handle_sets (trm_set (trm_bvar 0) (trm_null)) =
              SomeE (trm_setcar (trm_bvar 0) trm_null).
Proof.
  reflexivity. Qed.