From vchez Require Export Definitions.
From vchez Require Export Helpers.
From TLC Require Export LibVar.
From TLC Require Export LibFset.
From Coq Require Import List.
Import ListNotations.


(* reworking semantics with new definitions
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

Fixpoint get_sf_pps sfs :=
  match sfs with
  | nil => empty
  | sf :: sfs' => match sf with
                  | store_cons pp v => \{pp} \u (get_sf_pps sfs')
                  | _ => get_sf_pps sfs'
                  end
  end.

Fixpoint get_val x sfs :=
  match sfs with 
  | nil => NoneE "Var not in store"
  | sf :: sfs' => match sf with
                  | store_val y v => if (var_compare x y) 
                                     then SomeE v 
                                     else get_val x sfs'
                  | store_bh y => if (var_compare x y) 
                                  then NoneE "Tried to access bh value" 
                                  else get_val x sfs'
                  | store_cons _ _ => get_val x sfs'
                  end
  end.

Fixpoint get_pair pp sfs :=
  match sfs with 
  | nil => NoneE "Pair pointer not in store"
  | sf :: sfs' => match sf with
                  | store_cons pp' p => if (var_compare pp pp')
                                           then SomeE p
                                           else get_pair pp sfs'
                  | _ => get_pair pp sfs'
                  end
  end.

Definition get_fresh sfs t :=
  var_gen ((get_sf_vars sfs) \u (s_fv t)).

Definition get_fresh_pp sfs :=
  var_gen (get_sf_pps sfs).

Definition get_fresh_list sfs ts :=
  var_gen ((get_sf_vars sfs) \u (s_fvs ts)).

Fixpoint update_sf_var sfs x v :=
  match sfs with 
  | nil => sfs
  | sf :: sfs' => match sf with
                  | store_val y _ => if (var_compare x y) 
                                     then (store_val y v :: sfs')
                                     else sf :: (update_sf_var sfs' x v)
                  | store_bh y => if (var_compare x y) 
                                     then (store_val y v :: sfs')
                                     else sf :: (update_sf_var sfs' x v)
                  | store_cons _ _ => sf :: (update_sf_var sfs' x v)
                  end
  end.


Fixpoint update_sf_pp_car sfs pp v := 
  match sfs with 
  | nil => sfs
  | sf :: sfs' => match sf with
                  | store_cons pp' p => if (var_compare pp pp')
                                        then match p with
                                             | s_trm_cons v1 v2 => (store_cons pp (s_trm_cons v v2) :: sfs')
                                             | _ => sfs
                                             end
                                        else sf :: (update_sf_pp_car sfs' pp v)
                  | _ => sf :: (update_sf_pp_car sfs' pp v)
                  end
  end.

Fixpoint update_sf_pp_cdr sfs pp v := 
  match sfs with 
  | nil => sfs
  | sf :: sfs' => match sf with
                  | store_cons pp' p => if (var_compare pp pp')
                                        then match p with
                                             | s_trm_cons v1 v2 => (store_cons pp (s_trm_cons v1 v) :: sfs')
                                             | _ => sfs
                                             end
                                        else sf :: (update_sf_pp_cdr sfs' pp v)
                  | _ => sf :: (update_sf_pp_cdr sfs' pp v)
                  end
  end.

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
               (s_open_each ts x)))

  | step_var : (* get a variable's value from store *)
    forall s x v,
    get_val x s = SomeE v -> 
    step s (s_trm_fvar x)
         s v
  
  (* although set! can be called on bvars, 
     there is no semantic rule because such set!s only have meaning after substitution *)
  | step_set : (* set a fvar's value in store *)
    forall s x v,
    s_val v -> 
    step s  (s_trm_set (s_trm_fvar x) v)
         (update_sf_var s x v) (s_trm_null)

  | step_beginv : (* removes values from the front of a begin *)
    forall s v ts,
    s_val v ->
    step s (s_trm_begin (v :: ts))
         s (s_trm_begin ts)
        
  | step_begin_single : (* a single term in a begin reduces to just that term *)
    forall s t,
    step s (s_trm_begin (t :: nil))
         s t

  | step_cons_store : (* puts a cons into store *)
    forall s v1 v2 fresh_pp,
    s_val v1 ->
    s_val v2 ->
    fresh_pp = get_fresh_pp s ->
    step s (s_trm_cons v1 v2)
         ((store_cons fresh_pp (s_trm_cons v1 v2)) :: s) (s_trm_pp fresh_pp)

  | step_car :
    forall s pp p v1 v2,
    get_pair pp s = SomeE p ->
    p = s_trm_cons v1 v2 ->
    step s (s_trm_car (s_trm_pp pp))
         s v1

  | step_cdr :
    forall s pp p v1 v2,
    get_pair pp s = SomeE p ->
    p = s_trm_cons v1 v2 ->
    step s (s_trm_car (s_trm_pp pp))
         s v2
    
  | step_setcar :
    forall s pp v,
    s_val v ->
    step s  (s_trm_setcar (s_trm_pp pp) v) 
         (update_sf_pp_car s pp v) (s_trm_null)
  
  | step_setcdr :
    forall s pp v,
    s_val v ->
    step s  (s_trm_setcdr (s_trm_pp pp) v)
         (update_sf_pp_cdr s pp v) (s_trm_null).

Hint Constructors step.

Inductive multi_step : sfs -> s_trm -> sfs -> s_trm -> Prop :=
  | mstep_none :
    forall s t,
    multi_step s t s t

  | mstep_one :
    forall s1 t1 s2 t2,
    step s1 t1 s2 t2 ->
    multi_step s1 t1 s2 t2
  
  | mstep_trans :
    forall s1 t1 s2 t2 s3 t3,
    multi_step s1 t1 s2 t2 -> multi_step s2 t2 s3 t3 ->
    multi_step s1 t1 s3 t3.

Hint Constructors multi_step.

Lemma steps_context :
  forall C s e s' e',
  eval_ctx C ->
  multi_step s e s' e' ->
  multi_step s (C e) s' (C e').
Proof.
  intros. induction H0; eauto.
Qed.

*)