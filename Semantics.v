From vchez Require Export Definitions.
From vchez Require Export Helpers.
From TLC Require Export LibVar.
From TLC Require Export LibFset.
From Coq Require Import List.
Import ListNotations.

(*
r6rs semantics
use subst from definitions
*)

Inductive sf : Set :=
  | store_val (x : var) (v : s_trm)
  | store_bh  (x : var)
  | store_cons (pp : var) (v : s_trm).

Definition sfs := list sf.

Fixpoint get_sf_vars sfs :=
  match sfs with
  | nil => empty
  | sf :: sfs' => match sf with 
                  | store_val x v => \{x} \u (get_sf_vars sfs')
                  | store_bh x => \{x} \u (get_sf_vars sfs')
                  | store_cons _ _ => get_sf_vars sfs'
                  end
  end.

Definition get_fresh sfs t :=
  var_gen ((get_sf_vars sfs) \u (s_fv t)).

Definition get_fresh_list sfs ts :=
  var_gen ((get_sf_vars sfs) \u (s_fvs ts)).


Inductive prog : Set :=
  | s_prog (sfs : sf) (e : s_trm).

Inductive eval_ctx : (s_trm -> s_trm) -> Prop :=
  | ECHole : eval_ctx (fun E => E)
  | ECSet : forall x, eval_ctx (fun E => s_trm_set x E)
  | ECBegin : forall t ts, eval_ctx (fun E => s_trm_begin (E :: (t :: ts)))
  | ECApp : forall v,
            s_val v -> 
            eval_ctx (fun E => s_trm_app v E).

Hint Constructors eval_ctx.

(* Notation "` P sfs [ t ]" := (s_prog sfs (fill_ec ec_hole t)) (at level 70).
Notation "' P sfs F [ t ]" := (s_prog sfs (fill_ec F t)) (at level 70). *)

Inductive step : sfs -> s_trm -> sfs -> s_trm -> Prop :=
  | step_ctx : 
    forall C s e s' e',
    eval_ctx C -> (*C is a valid eval ctx*)
    s_term e -> s_term e' -> (* e and e' are well formed terms *)
    step s e   s' e' -> (* a step outside of a context *)
    step s (C e)  s' (C e') (* implies the step applies inside a context *)

  | step_mark1 : (* pull right term out of an application into a lambda for eval *)
    forall s e1 e2,
    s_term (s_trm_app e1 e2) ->
    s_term (s_trm_app (s_trm_abs [s_trm_app e1 (s_trm_bvar 0)]) e2) ->
    step s (s_trm_app e1 e2) (* (e1 e2)*)
         s (s_trm_app (s_trm_abs [s_trm_app e1 (s_trm_bvar 0)]) e2) (* ((lam (e1 0) e2) *)
  
  | step_mark2 : (* if right term is already a value, pull left term out *)
    forall s v e,
    s_val v ->
    s_term (s_trm_app e v) ->
    s_term (s_trm_app (s_trm_abs [s_trm_app (s_trm_bvar 0) v]) e) -> 
    step s (s_trm_app e v) (* (e v) *)
         s (s_trm_app (s_trm_abs [s_trm_app (s_trm_bvar 0) v]) e) (* ((lam (0 v)) e)*)
    
  | step_app : (* lambda and a value -> do subst *)
    forall s v ts x,
    s_val v ->
    x \notin ((get_sf_vars s) \u (s_fvs ts)) ->
    s_term (s_trm_app (s_trm_abs ts) v) ->
    s_term (s_trm_begin (s_substs x v (s_open_each ts x))) ->
    step s (s_trm_app (s_trm_abs ts) v)
         s (s_trm_begin 
             (s_substs 
               x
               v
               (s_open_each ts x))).
