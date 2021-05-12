From vchez Require Import Definitions.
From vchez Require Import Semantics.
From vchez Require Import Helpers.
From Coq Require Import List.
From Metalib Require Import LibTactics.

Hint Constructors s_trm.
Hint Constructors s_term.

(* Properties of local closure *)
Lemma s_term_abs_to_body : forall ts,
  s_term (s_trm_abs ts) -> s_body ts.
Proof.
  intros. unfold s_body. inversion H.
  exists L. intros. apply H1. apply H2. Qed.

Lemma s_body_to_term_abs : forall ts,
  s_body ts -> s_term (s_trm_abs ts).
Proof.
  intros. inversion H. apply s_term_abs with (L := x).
  apply H0.
Qed. 

Hint Resolve s_term_abs_to_body s_body_to_term_abs.

Lemma s_subst_id : forall t x u,
  x \notin s_fv t -> [x ~> u]t = t.
Proof.
  intros.
  induction t using s_trm_mutind with 
  (P := fun t => x `notin` s_fv t -> [x ~> u] t = t);
    intros; simpl; 
    try reflexivity.
    - induction x0. reflexivity. simpl in H. 
      apply notin_singleton_1' in H. 
      destruct (x0 == x). contradiction. reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
      simpl in H. 
      + apply notin_union_2 in H. apply H.
      + apply notin_union_1 in H. apply H.
    - f_equal. simpl in H. induction ts. reflexivity.
      assert (x `notin` s_fv a -> [x ~> u] a = a).
        { apply Forall_inv in H0. apply H0. }
      rewrite H1. f_equal. apply IHts.
      + apply Forall_inv_tail in H0. apply H0.
      + apply notin_union_2 in H. apply H.
      + apply notin_union_1 in H. apply H.
    - f_equal. simpl in H. induction ts. reflexivity.
      assert (x `notin` s_fv a -> [x ~> u] a = a).
        { apply Forall_inv in H0. apply H0. }
      rewrite H1. f_equal. apply IHts.
      + apply Forall_inv_tail in H0. apply H0.
      + apply notin_union_2 in H. apply H.
      + apply notin_union_1 in H. apply H.
    - f_equal. simpl in H. induction ts. reflexivity.
      assert (x `notin` s_fv a -> [x ~> u] a = a).
        { apply Forall_inv in H0. apply H0. }
      rewrite H1. f_equal. apply IHts.
      + apply Forall_inv_tail in H0. apply H0.
      + apply notin_union_2 in H. apply H.
      + apply notin_union_1 in H. apply H.
Qed.

(* programs are either values, stuck, or decompose uniquely into an ec and a reducible term *)
Theorem unique_ec :
  forall s t,
  s_term t -> (* no standalone bvars *)
  value t \/
  ~(exists s' t', step s t s' t') \/
  (exists C t' s' t'',
    eval_ctx C ->
    t = (C t') -> 
    step s (C t') s' t'').
Proof.
  intros. 
  induction t using s_trm_mutind. (* use our custom induction principle to get *)
  - destruct x. (*s_trm_var case*)
    + right. left. inversion H. (* standalone bvar -> False by s_term def *)
    + right. right. (* standalone fvar steps to put itself in store *)  
      exists (id). (* hole is just itself *)
      exists (s_trm_var (fvar x)).
      exists s.
      exists (match (get_val x s) with
              | SomeE v => v
              | NoneE e => s_trm_err e
              end).
     intros. 
     remember (get_val x s). destruct o.
     * compute. apply step_var. symmetry. apply Heqo.
     * compute. apply step_var_err. symmetry. apply Heqo.
  - destruct IHt2. inversion H. apply H3.      
       
   try (left; repeat constructor).

  
  
       
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
     
    
    

(*
To Prove:
  Unique Eval Contexts:
    term t -> decomp t ec1 -> decomp t ec2 -> ec1 = ec2
  
  
  
  *)







