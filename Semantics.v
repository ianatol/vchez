From vchez Require Import Definitions.
From vchez Require Export Helpers.
From Coq Require Import List.
From Coq Require Import Strings.String.
From Metalib Require Import Metatheory.
From Metalib Require Import MetatheoryAtom.
Import ListNotations.

Inductive sf : Set :=
  | store_val (x : var) (v : s_trm)
  | store_bh  (x : var)
  | store_cons (pp : var) (v1 : s_trm) (v2 : s_trm).

Definition sfs := list sf.

Fixpoint get_sf_vars sfs :=
  match sfs with
  | nil => empty
  | sf :: sfs' => match sf with 
                  | store_val x v => {{x}} \u (get_sf_vars sfs')
                  | store_bh x => {{x}} \u (get_sf_vars sfs')
                  | store_cons _ _ _ => get_sf_vars sfs'
                  end
  end.

Fixpoint get_sf_pps sfs :=
  match sfs with
  | nil => empty
  | sf :: sfs' => match sf with
                  | store_cons pp _ _ => {{pp}} \u (get_sf_pps sfs')
                  | _ => get_sf_pps sfs'
                  end
  end.

Fixpoint get_val x sfs :=
  match sfs with 
  | nil => NoneE "Var not in store"
  | sf :: sfs' => match sf with
                  | store_val y v => if (x == y) 
                                     then SomeE v 
                                     else get_val x sfs'
                  | store_bh y => if (x == y) 
                                  then NoneE "Tried to access bh value" 
                                  else get_val x sfs'
                  | store_cons _ _ _ => get_val x sfs'
                  end
  end.

Fixpoint get_pair pp sfs :=
  match sfs with 
  | nil => NoneE "Pair pointer not in store"
  | sf :: sfs' => match sf with
                  | store_cons pp' v1 v2 => if (pp == pp')
                                           then SomeE (v1, v2)
                                           else get_pair pp sfs'
                  | _ => get_pair pp sfs'
                  end
  end.


Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => {{ x }}) in
  let C := gather_vars_with (fun x : s_trm => s_fv x) in
  let D := gather_vars_with (fun x : sfs => get_sf_vars x) in
  constr:(A \u B \u C \u D).


Tactic Notation "pick_fresh" ident(x) :=
  let L := gather_vars in pick_fresh_gen L x.
Tactic Notation "pick_fresh" ident(x) "from" constr(E) :=
  let L := gather_vars in pick_fresh_gen (L \u E) x.

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Hint Constructors s_term.

Definition get_fresh (sfs : list sf) (t : s_trm) : var :=
  match atom_fresh ((get_sf_vars sfs) \u (s_fv t)) with
    (exist _ x _) => x
  end.

Definition get_fresh_list sfs ts :=
  match atom_fresh ((get_sf_vars sfs) \u (s_fvs ts)) with
    (exist _ x _ ) => x
  end.
  
Definition get_fresh_pp sfs :=
  match atom_fresh (get_sf_pps sfs) with
    (exist _ x _ ) => x
  end.

Fixpoint update_sf_var sfs x v :=
  match sfs with 
  | nil => sfs
  | sf :: sfs' => match sf with
                  | store_val y _ => if (x == y) 
                                     then (store_val y v :: sfs')
                                     else sf :: (update_sf_var sfs' x v)
                  | store_bh y => if (x == y) 
                                     then (store_val y v :: sfs')
                                     else sf :: (update_sf_var sfs' x v)
                  | store_cons _ _ _ => sf :: (update_sf_var sfs' x v)
                  end
  end.


Fixpoint update_sf_pp_car sfs pp v := 
  match sfs with 
  | nil => sfs
  | sf :: sfs' => match sf with
                  | store_cons pp' v1 v2 => if (pp == pp')
                                            then ((store_cons pp v v2) :: sfs')
                                            else sf :: (update_sf_pp_car sfs' pp v)
                  | _ => sf :: (update_sf_pp_car sfs' pp v)
                  end
  end.

Fixpoint update_sf_pp_cdr sfs pp v := 
  match sfs with 
  | nil => sfs
  | sf :: sfs' => match sf with
                  | store_cons pp' v1 v2 => if (pp == pp')
                                            then ((store_cons pp v1 v) :: sfs')
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
  | ECApp : forall v1,
            value v1 -> 
            eval_ctx (fun E => ` ( v1 ; E )).

Hint Constructors eval_ctx.

(* Notation "` P sfs [ t ]" := (s_prog sfs (fill_ec ec_hole t)) (at level 70).
Notation "' P sfs F [ t ]" := (s_prog sfs (fill_ec F t)) (at level 70). *)

Inductive step : sfs -> s_trm -> sfs -> s_trm -> Prop :=
  | step_ctx : 
    forall C s e s' e',
    eval_ctx C -> (*C is a valid eval ctx*)
    step s e   s' e' -> (* a step outside of a context *)
    step s (C e)  s' (C e') (* implies the step applies inside a context *)

  | step_mark1 : (* pull left terms out of a sequence into a lambda for eval *)
    forall s e es, s_term e -> s_terms es -> ~ (value e) ->
    step s (s_trm_seq (e :: es)) (* (e es ...)*)
         s (s_trm_seq 
             [(s_trm_abs [(s_trm_seq ((s_trm_var (bvar 0)) :: es))]) ; e]) (* ((lam (0 es ...) e) *)
  
  | step_mark2 : (* if term is surrounded by values, pull it out *)
    forall s vs1 vs2 e, vals vs1 -> vals vs2 -> s_term e ->
    step s (s_trm_seq (vs1 ++ [e] ++ vs2)) (* (vs1 ... e vs2 ...) *)
         s (s_trm_seq 
             [(s_trm_abs [s_trm_seq (vs1 ++ [s_trm_var (bvar 0)] ++ vs2)]) ; e])  (* ( (lam (vs1 ... 0 vs2 ...)) e) *)
    
  | step_app : (* lambda and a value -> do subst *)
    forall s v ts, value v -> s_term (s_trm_abs ts) ->
    step s ` ((s_trm_abs ts) ; v)
         s (s_trm_begin 
             (open_each ts v))

  | step_var : (* get a variable's value from store *)
    forall s x v,
    get_val x s = SomeE v -> 
    step s (s_trm_var (fvar x))
         s v
  
  (* although set! can be called on bvars, 
     there is no semantic rule because such set!s only have meaning after substitution *)
  | step_set : (* set a fvar's value in store *)
    forall s x v,
    value v -> 
    step s  (s_trm_set (s_trm_var (fvar x)) v)
         (update_sf_var s x v) (s_trm_null)

  | step_beginv : (* removes values from the front of a begin *)
    forall s v ts,
    value v ->
    step s (s_trm_begin (v :: ts))
         s (s_trm_begin ts)
        
  | step_begin_single : (* a single term in a begin reduces to just that term *)
    forall s t,
    step s (s_trm_begin (t :: nil))
         s t

  | step_cons_store : (* puts a cons into store *)
    forall s v1 v2 pp, value v1 -> value v2 ->
    pp = get_fresh_pp s -> 
    step s ` (s_trm_cons ; v1 ; v2)
         ((store_cons pp v1 v2) :: s) (s_trm_pp pp)

  | step_car :
    forall s pp v1 v2,
    get_pair pp s = SomeE (v1, v2) ->
    step s ` (s_trm_car ; (s_trm_pp pp))
         s v1

  | step_cdr :
    forall s pp v1 v2,
    get_pair pp s = SomeE (v1, v2) ->
    step s ` (s_trm_cdr ; (s_trm_pp pp))
         s v2
    
  | step_setcar :
    forall s pp v,
    value v ->
    step s  ` (s_trm_setcar ; (s_trm_pp pp) ; v) 
         (update_sf_pp_car s pp v) (s_trm_null)
  
  | step_setcdr :
    forall s pp v,
    value v ->
    step s  ` (s_trm_setcdr ; (s_trm_pp pp) ; v)
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

Inductive eval : s_trm -> s_trm -> Prop :=
  | eval_val : forall t1, value t1 -> eval t1 t1

  | eval_step : forall s1 t1 s2 t2,
    value t2 ->
    multi_step s1 t1 s2 t2 ->
    eval t1 t2.

Inductive vsr : sfs -> s_trm -> Prop :=
  | vsr_val : forall s t, value t -> vsr s t
  | vsr_stuck : forall s t, ~ (exists s' t', step s t s' t') -> vsr s t
  | vsr_reducible : forall C s t,
                    eval_ctx C ->
                    (exists s' t', step s t s' t') -> 
                    vsr s (C t).

Theorem vsr_preserve :
  forall s t,
  vsr s t -> 
  exists s' t', step s t s' t' ->
  vsr s' t.
Proof.
  intros. induction t; simpl.
Abort.


  
Theorem step_progress :
  forall s t, s_term t -> value t \/ (exists s' t', step s t s' t').
Proof.
  intros. induction t; try (left; constructor); right.
  - destruct ts.  
  Abort.
  - (* t = s_trm_seq ts *)
    