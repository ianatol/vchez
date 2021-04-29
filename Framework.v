From vchez Require Import Definitions.
From Coq Require Import List.
From Metalib Require Import LibTactics.

Hint Constructors s_trm.
Hint Constructors s_term.

(* Properties of local closure *)
Lemma s_term_abs_to_body : forall ts,
  s_term (s_trm_abs ts) -> s_body ts.
Proof.
  intros. unfold s_body. inversion H.
  exists L. apply H1. Qed.

Lemma s_body_to_term_abs : forall ts,
  s_body ts -> s_term (s_trm_abs ts).
Proof.
  intros. inversion H. pick fresh x0.
  apply s_term_abs with (L := x).
  intros. apply H0. apply H1.
Qed.

Hint Resolve s_term_abs_to_body s_body_to_term_abs.

Lemma s_subst_id : forall t x u,
  x \notin s_fv t -> [x ~> u]t = t.
Proof.
  intros.
  induction t using s_trm_mutind with 
  (P := fun t => x `notin` s_fv t -> [x ~> u] t = t);
  intros; simpl.
    - induction x0. reflexivity. simpl in H. 
      apply notin_singleton_1' in H. 
      destruct (x0 == x). contradiction. reflexivity.
    - rewrite IHt1. rewrite IHt2. reflexivity.
      simpl in H. 
      + apply notin_union_2 in H. apply H.
      + apply notin_union_1 in H. apply H.
    - f_equal. simpl in H. 
Abort. 
    
       

     
    
    

(*
To Prove:
  Unique Eval Contexts:
    term t -> decomp t ec1 -> decomp t ec2 -> ec1 = ec2
  
  
  
  *)







