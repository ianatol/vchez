From vchez Require Export Definitions.
From vchez Require Export Pass.
From Coq Require Import List.
Import ListNotations.

(* Examples of the convert-assignments pass working as intended *)

Example ca_1 : forall x,
  ca (s_trm_fvar x) = SomeE (t_trm_fvar x).
Proof. reflexivity. Qed.

Example ca_2 :
  ca (s_trm_abs [s_trm_set (s_trm_bvar 0) s_trm_true]) =
  SomeE (t_trm_abs
          [t_trm_let (t_trm_cons (t_trm_bvar 0) (t_trm_null))
            [t_trm_setcar (t_trm_bvar 0) t_trm_true]]).
Proof. reflexivity. Qed.

Example ca_6 :
  ca (s_trm_app 
       (s_trm_abs 
         [s_trm_set (s_trm_bvar 0) s_trm_true;
          s_trm_bvar 0])
        s_trm_false) =
  SomeE (t_trm_app 
          (t_trm_abs
            [t_trm_let (t_trm_cons (t_trm_bvar 0) (t_trm_null))
              [t_trm_setcar (t_trm_bvar 0) t_trm_true;
               t_trm_car (t_trm_bvar 0)]])
          t_trm_false).
Proof. reflexivity. Qed.

