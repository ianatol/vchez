From vchez Require Export Definitions.
From TLC Require Import LibLN.
From TLC Require Import LibReflect.
From Coq Require Export List.

Hint Constructors s_trm.
Hint Constructors s_term.

(* Properties of local closure *)
Lemma s_term_abs_to_body : forall ts,
  s_term (s_trm_abs ts) -> s_body ts.
Proof.
  intros. unfold s_body. inversion* H. Qed.

Lemma s_body_to_term_abs : forall ts,
  s_body ts -> s_term (s_trm_abs ts).
Proof.
  intros. inversion* H. Qed.

Hint Resolve s_term_abs_to_body  
             s_body_to_term_abs.

Lemma s_subst_id : forall t x u,
  x \notin s_fv t -> s_subst x u t = t.
Proof. Abort. 


     
    
    

(*
To Prove:
  Unique Eval Contexts:
    term t -> decomp t ec1 -> decomp t ec2 -> ec1 = ec2
  
  
  
  *)







