From Coq Require Import List.
From Coq Require Import Strings.String.
Import ListNotations.
Import Nat.

From Metalib Require Export Metatheory.

(*
Defines the syntax of our source and target languages,
as well as a capture-avoiding subsititution based on locally nameless bindings
*)

(*
locally nameless variable bindings - 
  bound variables are represented by de Bruijn indices
  free variables are represented by names (implemented as numbers)

Cofinite Quantification
  relations that introduce a fresh variable define it via universal quantification
  forall x L, x \notin L 
  rather than existential quantification
  which gives us a stronger induction hypothesis
*)

(* Implicit Types x y z : var. *)

(*
pre terms may contain non locally closed terms
these are terms that are introduced by the locally nameless style,
but are invalid lc terms
i.e. (bvar 1) with no context
*)

Inductive ln_var : Set :=
  | bvar (i : nat)
  | fvar (x : var).

(*source langauge pre-terms*)
Inductive s_trm : Set :=
  (* non-values *)
  | s_trm_seq  (ts : list s_trm)
  | s_trm_begin (ts : list s_trm)
  | s_trm_set (x : s_trm)(t : s_trm)
  | s_trm_var (x : ln_var)

  (* values *)
  | s_trm_abs (ts : list s_trm) (*binding is implicit because of debruijn indices*)
  | s_trm_setcar 
  | s_trm_setcdr 
  | s_trm_cons
  | s_trm_car 
  | s_trm_cdr
  | s_trm_pp (n : var)
  | s_trm_num (i : nat)
  | s_trm_err (e : string)
  | s_trm_null
  | s_trm_true
  | s_trm_false.

Hint Constructors s_trm.

Notation "` ( t ) " := (s_trm_seq [t]).
Notation "` ( t1 ; t2 ; .. ; t3 )" := (s_trm_seq (cons t1 (cons t2 .. (cons t3 nil) ..))).

Definition let_ v es :=
  ` ( (s_trm_abs es) ; v).


Theorem s_trm_mutind
 : forall 
    (P : s_trm -> Prop),
    (forall x , P (s_trm_var x)) ->
    (forall x t, P x -> P t -> P(s_trm_set x t)) -> 
    (forall ts, Forall P ts -> P (s_trm_seq ts)) ->
    (forall ts, Forall P ts -> P (s_trm_begin ts)) ->
    (forall ts, Forall P ts -> P (s_trm_abs ts)) ->
    (forall n : atom, P (s_trm_pp n)) ->
    (forall i : nat, P (s_trm_num i)) ->
    (forall s : string, P (s_trm_err s)) ->
    P s_trm_setcar ->
    P s_trm_setcdr ->
    P s_trm_cons ->
    P s_trm_car ->
    P s_trm_cdr ->
    P s_trm_null -> 
    P s_trm_true -> 
    P s_trm_false -> 
    forall s : s_trm, P s.
Proof.
  intro P.
  intros var set seq begin abs pp num err setcar setcdr cons car cdr null true false.
  refine (fix IH t : P t := _).
  case t; intros; try assumption.
  - apply seq. induction ts; intuition.
  - apply begin. induction ts; intuition.
  - apply set. apply IH. apply IH.
  - apply var.
  - apply abs. induction ts; intuition.
  - apply pp.
  - apply num.
  - apply err. 
Qed.

(* values in source language *)
Inductive value : s_trm -> Prop :=
  | val_abs : forall ts,
      value (s_trm_abs ts)
  | val_setcar : value (s_trm_setcar)
  | val_setcdr : value (s_trm_setcdr)
  | val_cons : value (s_trm_cons)
  | val_car : value (s_trm_car)
  | val_cdr : value (s_trm_cdr)
  | val_pp : forall n, value (s_trm_pp n)
  | val_num : forall i, value (s_trm_num i)
  | val_err : forall e, value (s_trm_err e)
  | val_null : value (s_trm_null)
  | val_true : value (s_trm_true)
  | val_false : value (s_trm_false)
  
with vals : list s_trm -> Prop :=
  | vals_nil : vals([])
  | vals_single : forall t, value t -> vals [t]
  | vals_next : 
      forall t ts,
        vals ts -> 
        value t ->
        vals (t :: ts).


(* 
Opening a trm t with a trm u containing a fresh free variable x.
  so u = (s_trm_var (fvar x))
To do so, we replace all references to local bvar with u.
This means we have to keep track of the current level of abstraction with k
So we are replacing all (bvar k) with (fvar x), and incrementing k with abstraction levels
*)

Definition open_var v (k : nat) (u t : s_trm) :=
  match v with
  | bvar i => if (k == i) then u else t
  | fvar x => t
  end.

Fixpoint s_open_rec (k : nat) (u : s_trm) (t : s_trm) {struct t} : s_trm :=
  match t with
  (* for lists of terms that don't abstract, just apply open to all terms *)
  | s_trm_seq ts => s_trm_seq (List.map (s_open_rec k u) ts)
  | s_trm_begin ts => s_trm_begin (List.map (s_open_rec k u) ts)

  (* since lambda abstracts, add a layer of depth *)
  | s_trm_abs ts => let s_open_rec_S := (s_open_rec (S k) u) in
                    s_trm_abs (List.map s_open_rec_S ts)
  
  (* for set!, just apply open to args*)
  | s_trm_set x t1 => s_trm_set (s_open_rec k u x) (s_open_rec k u t1)

  (* replace bound variables at the current level of abstraction with u *)
  | s_trm_var v => match v with
                   | bvar i => if (k == i) then u else t
                   | fvar x => t
                   end
  (* nothing else contains bound variables *)
  | _ => t
  end.

(* open a term t with another term u at base level of abstraction *)
Definition open t u := s_open_rec 0 u t.

Fixpoint open_each ts u :=
  match ts with
  | [] => []
  | t :: ts' => (open t u) :: (open_each ts' u)
  end.

(* open a term t with some fvar x *)
Notation "t ^^ x" := (open t (s_trm_var (fvar x))) (at level 67).

(* open each term in a list with a fvar x*)
Fixpoint s_open_each ts x :=
  match ts with
  | [] => []
  | t :: ts' => (t ^^ x) :: s_open_each ts' x
  end.

(*
Closing a term is the inverse of opening.
Replaces a free var z with bvar k where k is the current level of abstraction
*)
Fixpoint s_close_var_rec (k : nat) (z : var) (t : s_trm) {struct t} : s_trm :=
  match t with
  (* seq and begin don't abstract, so just call on each term *)
  | s_trm_seq ts => s_trm_seq (List.map (s_close_var_rec k z) ts)
  | s_trm_begin ts => s_trm_begin (List.map (s_close_var_rec k z) ts)

  (* lambda abstracts, so increment depth and then call on each term *)
  | s_trm_abs ts => let s_close_var_rec_S := (s_close_var_rec (S k) z) in
                    s_trm_abs (List.map s_close_var_rec_S ts)

  (* apply close to set's variable and body *)
  | s_trm_set x t1 => s_trm_set (s_close_var_rec k z x) (s_close_var_rec k z t1)

  (* replace fvar z with bvar k *)
  | s_trm_var v => match v with
                   | fvar x => if (x == z) then (s_trm_var (bvar k)) else t
                   | bvar _ => t
                   end
  | _ => t
  end.


(* replace fvar z's in t with bound variables at their appropriate depth *)
Definition s_close_var z t := s_close_var_rec 0 z t.

Inductive non_empty {A : Type} : list A -> Prop := 
  | ne_list : 
    forall l n, length l = S n -> non_empty l.

(* terms are well formed (locally closed) if there are no bvars referring to invalid depth 
   we determine this by opening all abstractions with a fresh variable
   if there are bound vars left over, the term is not locally closed 
   
   also if ts are non-empty *)
Inductive s_term : s_trm -> Prop :=
  (* if the body of an abs is well formed after opening its terms with a fresh variable, 
      it is well formed *)
  | s_term_abs : forall L ts,
      (forall x, x \notin L -> s_terms (s_open_each ts x)) ->
      s_term (s_trm_abs ts)

  (* if each term in a begin is well-formed, then it is well formed
     don't open with a fresh variable because bvars are not allowed in a begin
     i.e. the program (begin (bvar 0)) is NOT well formed *)
  | s_term_begin : forall ts,
      s_terms ts ->
      s_term (s_trm_begin ts)
  
  (* same for seq and set *)
  | s_term_seq : forall ts,
      s_terms ts -> 
      s_term (s_trm_seq ts)

  | s_term_set : forall b t,
      s_term b -> s_term t -> s_term (s_trm_set b t)

  (* fvars are locally closed. bvars are not!*)
  | s_term_var : forall x,
      s_term (s_trm_var (fvar x))

  (* everything else is locally closed *)

  | s_term_setcar : s_term (s_trm_setcar)
  | s_term_setcdr : s_term (s_trm_setcdr)
  | s_term_cons : s_term (s_trm_cons)
  | s_term_car : s_term (s_trm_car)
  | s_term_cdr : s_term (s_trm_cdr)
  | s_term_pp : forall n, s_term (s_trm_pp n)
  | s_term_num : forall i, s_term (s_trm_num i)
  | s_term_null : s_term (s_trm_null)
  | s_term_true : s_term (s_trm_true)
  | s_term_false : s_term (s_trm_false)

with s_terms : list s_trm -> Prop :=
  | s_terms_single : forall t, s_term t -> s_terms [t]
  | s_terms_next : 
      forall t ts,
        s_terms ts -> 
        s_term t ->
        s_terms (t :: ts).

(* Body of an abstraction *)
Definition s_body ts :=
  exists L, forall x, x \notin L ->
  s_terms (s_open_each ts x).

(* Free variables of a term. Collect all fvars in a set*)
Fixpoint s_fv (t : s_trm) : vars :=
  let fix fvs' (ts : list s_trm) : vars :=
    match ts with
    | [] => {}
    | t :: ts' => s_fv t \u fvs' ts'
    end
  in
    match t with
    | s_trm_var v => match v with
                     | fvar y => {{ y }}
                     | bvar _ => {}
                     end
    | s_trm_abs ts => fvs' ts
    | s_trm_begin ts => fvs' ts
    | s_trm_seq ts => fvs' ts
    | s_trm_set x t1 => (s_fv x) \u (s_fv t1)
    | _ => {}
    end.

Fixpoint s_fvs ts :=
  match ts with
  | [] => {}
  | t :: ts' => s_fv t \u s_fvs ts'
  end.

Fixpoint s_subst (z : var) (u : s_trm) (t : s_trm) {struct t} : s_trm :=
  let fix substs (ts : list s_trm) :=
    match ts with
    | [] => []
    | t' :: ts' => (s_subst z u t') :: (substs ts')
    end
  in
  match t with
  | s_trm_var v => match v with
                   | fvar x => if (x == z) then u else t
                   | bvar _ => t
                   end
  | s_trm_abs ts => s_trm_abs (substs ts)
  | s_trm_begin ts => s_trm_begin (substs ts)
  | s_trm_seq ts => s_trm_seq (substs ts)
  | s_trm_set x t1 => s_trm_set (s_subst z u x) (s_subst z u t1)
  | _ => t
  end.

Fixpoint s_substs z u ts :=
  match ts with
  | [] => []
  | t' :: ts' => (s_subst z u t') :: (s_substs z u ts')
  end.

Notation "[ z ~> u ] t" := (s_subst z u t) (at level 68).

Definition sum (l : list nat) :=
  fold_left (plus) l 0.

Fixpoint s_trm_size (t : s_trm) {struct t} : nat :=
  match t with
  | s_trm_abs ts => 1 + (sum (List.map s_trm_size ts))
  | s_trm_begin ts => 1 + (sum (List.map s_trm_size ts))
  | s_trm_seq ts => 1 + (sum (List.map s_trm_size ts))
  | s_trm_set x t1 => 1 + (s_trm_size x) + (s_trm_size t1)
  | _ => 1
  end.
