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
  intros. inversion H. Abort.

Hint Resolve s_term_abs_to_body.

Lemma s_subst_id : forall t x u,
  x \notin s_fv t -> [x ~> u]t = t.
Proof. Abort.

     
    
    

(*
To Prove:
  Unique Eval Contexts:
    term t -> decomp t ec1 -> decomp t ec2 -> ec1 = ec2
  
  
  
  *)







