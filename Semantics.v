From vchez Require Export Definitions.
From vchez Require Export Helpers.
From Coq Require Import List.
Import ListNotations.

(*
r6rs semantics
use subst from definitions
*)

Inductive stre : Set :=
  | store_val (x : var) (v : s_trm)
  | store_bh  (x : var)
  | store_cons (pp : var) (v : s_trm).

Definition sf := list stre.

Inductive prog : Set :=
  | s_prog (sfs : sf) (e : s_trm).

Inductive ec_p : Set :=
  | ec_prog (sfs : sf) (f : ec_f)

with ec_f : Set := 
  | ec_hole
  | ec_set (x : s_trm) (hole : ec_f)
  | ec_begin_ts (hole : ec_f) (ts : list s_trm)
  | ec_begin_vs (vs : list s_trm) (hole : ec_f) (ts : list s_trm).

Fixpoint fill_ec (F : ec_f) (t : s_trm) :=
  match F with 
  | ec_hole => t
  | ec_set x F' => s_trm_set x (fill_ec F' t)
  | ec_begin_ts F' ts => s_trm_begin ((fill_ec F' t) :: ts)
  | ec_begin_vs vs F' ts => s_trm_begin (vs ++ (fill_ec F' t) :: ts)
  end.
  

Notation "' P sfs F [ t ]" := (s_prog sfs (fill_ec F t)) (at level 70).
(* 
Reserved Notation " t '|->' t' " (at level 71).

Inductive small_step : ec_p -> ec_p -> Prop :=
  | ss_cons : forall F v1 v2,
      s_val v1 ->
      s_val v2 ->
      ' P sfs F [ s_trm_cons v1 v2] |->
      ' P 
*)