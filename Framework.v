From vchez Require Export Definitions.
From TLC Require Import LibLN.
From Coq Require Export List.

Hint Constructors term : core.

Notation "'[[' x '~>' y ']]' t" := (subst x (trm_fvar y) t) (at level 69).

(* Properties of local closure *)
Lemma term_abs_to_body : forall ts,
  term (trm_abs ts) -> body ts.
Proof.
  intros. unfold body. inversion* H. Qed.

Lemma body_to_term_abs : forall ts,
  body ts -> term (trm_abs ts).
Proof.
  intros. inversion* H. Qed.

Hint Resolve term_abs_to_body body_to_term_abs.

Lemma subst_fresh_ts : forall x ts u,
  x \notin fvs ts -> (map (subst x u) ts) = ts.
Proof.
  intros. Abort.

  
(* Properties of subst *)
Lemma subst_fresh : forall x t u,
  x \notin fv t -> (subst x u t) = t.
Proof.
  intros.
Abort.

(*
To Prove:
  Unique Eval Contexts:
    term t -> decomp t ec1 -> decomp t ec2 -> ec1 = ec2
  
  
  
  *)







