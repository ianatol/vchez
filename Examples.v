From vchez Require Export Definitions.
From vchez Require Export Pass.
From vchez Require Export Semantics.
From vchez Require Import Helpers.
From TLC Require Import LibTactics.

From Coq Require Import List.
Import ListNotations.


(*Semantics examples*)

Example sem1 : forall sfs v1 v2 pp,
  value v1 -> value v2 ->
  pp = get_fresh_pp sfs ->
  multi_step sfs ` (s_trm_car ; ` (s_trm_cons ; v1 ; v2))
             ((store_cons pp v1 v2) :: sfs) v1.
Proof.
  intros.
  eapply mstep_trans.
  (* first step *)
    apply mstep_one. 
    lets D1: step_ctx (ECApp s_trm_car (val_car)).
    eapply D1.
    apply step_cons_store; try assumption.
    eapply H1.
  (* second step *)
  apply mstep_one.
  apply step_car with (v1 := v1) (v2 := v2).
  simpl. subst. unfold get_fresh_pp. Abort. 
  
(*
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
*)