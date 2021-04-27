From Coq Require Import List.
Import ListNotations.
Import Nat.

From TLC Require Export LibFix.
From TLC Require Export LibVar.
From TLC Require Export LibFset.

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

Implicit Types x y z : var.

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
  | s_trm_null
  | s_trm_true
  | s_trm_false.

Notation "` ( t ) " := (s_trm_seq [t]).
Notation "` ( t1 ; t2 ; .. ; t3 )" := (s_trm_seq (cons t1 (cons t2 .. (cons t3 nil) ..))).

(* target language pre-terms
   add let, set! is now only on free vars, so call it set_top *)
Inductive t_trm : Set :=
  (* non-values *)
  | t_trm_seq (ts : list t_trm)
  | t_trm_begin (ts : list t_trm)
  | t_trm_set_top (x : t_trm) (t : t_trm)
  | t_trm_var (x : ln_var)
  | t_trm_let (v : t_trm) (ts : list t_trm)

  (* values *)
  | t_trm_abs  (ts : list t_trm)
  | t_trm_setcar
  | t_trm_setcdr
  | t_trm_cons
  | t_trm_car 
  | t_trm_cdr 
  | t_trm_pp (n : var)
  | t_trm_num (i : nat)
  | t_trm_null
  | t_trm_true
  | t_trm_false.

Notation "$ { t } " := (t_trm_seq [t]).
Notation "$ { t1 ; t2 ; .. ; t3 }" := (t_trm_seq (cons t1 (cons t2 .. (cons t3 nil) ..))).
  

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
  | sval_null : value (s_trm_null)
  | sval_true : value (s_trm_true)
  | sval_false : value (s_trm_false)
  
with vals : list s_trm -> Prop :=
  | vals_nil : vals([])
  | vals_single : forall t, value t -> vals [t]
  | vals_next : 
      forall t ts,
        vals ts -> 
        value t ->
        vals (t :: ts).

(*
Inductive t_val : t_trm -> Prop :=
  | tval_abs : forall ts,
      t_val (t_trm_abs ts)
  | tval_pp : forall n,
      t_val (t_trm_pp n)
  | tval_num : forall i,
      t_val (t_trm_num i)
  | tval_null : t_val (t_trm_null)
  | tval_true : t_val (t_trm_true)
  | tval_false : t_val (t_trm_false).
*)

(* 
Opening a trm t with a trm u containing a fresh free variable x.
  so u = (s_trm_var (fvar x))
To do so, we replace all references to local bvar with u.
This means we have to keep track of the current level of abstraction with k
So we are replacing all (bvar k) with (fvar x), and incrementing k with abstraction levels
*)

Definition open_var v k (u t : s_trm) :=
  match v with
  | bvar i => if (k =? i) then u else t
  | fvar x => t
  end.

Fixpoint s_open_rec (k : nat) (u : s_trm) (t : s_trm) {struct t} : s_trm :=
  match t with
  (* for lists of terms that don't abstract, just apply open to all terms *)
  | s_trm_seq ts => s_trm_seq (map (s_open_rec k u) ts)
  | s_trm_begin ts => s_trm_begin (map (s_open_rec k u) ts)

  (* since lambda abstracts, add a layer of depth *)
  | s_trm_abs ts => let s_open_rec_S := (s_open_rec (S k) u) in
                    s_trm_abs (map s_open_rec_S ts)
  
  (* for set!, just apply open to args*)
  | s_trm_set x t1 => s_trm_set (s_open_rec k u x) (s_open_rec k u t1)

  (* replace bound variables at the current level of abstraction with u *)
  | s_trm_var v => match v with
                   | bvar i => if (k =? i) then u else t
                   | fvar x => t
                   end
  (* nothing else contains bound variables *)
  | _ => t
  end.

(* open a term t with another term u at base level of abstraction *)
Definition open t u := s_open_rec 0 u t.

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
  | s_trm_seq ts => s_trm_seq (map (s_close_var_rec k z) ts)
  | s_trm_begin ts => s_trm_begin (map (s_close_var_rec k z) ts)

  (* lambda abstracts, so increment depth and then call on each term *)
  | s_trm_abs ts => let s_close_var_rec_S := (s_close_var_rec (S k) z) in
                    s_trm_abs (map s_close_var_rec_S ts)

  (* apply close to set's variable and body *)
  | s_trm_set x t1 => s_trm_set (s_close_var_rec k z x) (s_close_var_rec k z t1)

  (* replace fvar z with bvar k *)
  | s_trm_var v => match v with
                   | fvar x => if var_compare x z then (s_trm_var (bvar k)) else t
                   | bvar _ => t
                   end
  | _ => t
  end.


(* replace fvar z's in t with bound variables at their appropriate depth *)
Definition s_close_var z t := s_close_var_rec 0 z t.

(* terms are well formed (locally closed) if there are no bvars referring to invalid depth 
   we determine this by opening all abstractions with a fresh variable
   if there are bound vars left over, the term is not locally closed *)
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
      s_terms ts -> s_term (s_trm_begin ts)
  
  (* same for seq and set *)
  | s_term_seq : forall ts,
      s_terms ts -> s_term (s_trm_seq ts)

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
  | s_terms_nil : s_terms ([])
  | s_terms_single : forall t, s_term t -> s_terms [t]
  | s_terms_next : 
      forall t ts,
        s_terms ts -> 
        s_term t ->
        s_terms (t :: ts).

(* Body of an abstraction *)
Definition s_body ts :=
  exists L, forall x, x \notin L -> s_terms (s_open_each ts x).

(* Free variables of a term. Collect all fvars in a set*)
Fixpoint s_fv (t : s_trm) : vars :=
  let fix fvs' (ts : list s_trm) : vars :=
    match ts with
    | [] => \{}
    | t :: ts' => s_fv t \u fvs' ts'
    end
  in
    match t with
    | s_trm_var v => match v with
                     | fvar y => \{y}
                     | bvar _ => \{}
                     end
    | s_trm_abs ts => fvs' ts
    | s_trm_begin ts => fvs' ts
    | s_trm_seq ts => fvs' ts
    | s_trm_set x t1 => (s_fv x) \u (s_fv t1)
    | _ => \{}
    end.

Fixpoint s_fvs ts :=
  match ts with
  | [] => \{}
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
                   | fvar x => if (var_compare x z) then u else t
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
  | s_trm_abs ts => 1 + (sum (map s_trm_size ts))
  | s_trm_begin ts => 1 + (sum (map s_trm_size ts))
  | s_trm_seq ts => 1 + (sum (map s_trm_size ts))
  | s_trm_set x t1 => 1 + (s_trm_size x) + (s_trm_size t1)
  | _ => 1
  end.



(* probably not needed target language stuff 

Fixpoint t_open_rec (k : nat) (u : t_trm) (t : t_trm) {struct t} : t_trm :=
  match t with
  | t_trm_bvar i => if (k =? i) then u else t
  | t_trm_fvar x => t
  | t_trm_abs ts => let t_open_rec_S := (t_open_rec (S k) u) in
                    t_trm_abs (map t_open_rec_S ts)
  | t_trm_let v ts => let t_open_rec_S := (t_open_rec (S k) u) in
                      t_trm_let (t_open_rec k u v) (map t_open_rec_S ts)
  | t_trm_set_top x t1 => t_trm_set_top x (t_open_rec k u t1)
  | t_trm_app t1 t2 => t_trm_app (t_open_rec k u t1)(t_open_rec k u t2)
  | t_trm_setcar p v => t_trm_setcar (t_open_rec k u p) (t_open_rec k u v)
  | t_trm_setcdr p v => t_trm_setcdr (t_open_rec k u p) (t_open_rec k u v)
  | t_trm_cons v1 v2 => t_trm_cons (t_open_rec k u v1)(t_open_rec k u v2)
  | t_trm_car p => t_trm_car (t_open_rec k u p)
  | t_trm_cdr p => t_trm_cdr (t_open_rec k u p)
  | t_trm_begin ts => let t_open_rec_S := (t_open_rec (S k) u) in
                      t_trm_begin (map t_open_rec_S ts)
  | _ => t
  end.

Notation "{ k ~>t u } t" := (t_open_rec k u t) (at level 67).

Definition t_open t u := t_open_rec 0 u t.

Notation "t ^^t u" := (t_open t u) (at level 67).
Notation "t ^t x" := (t_open t (t_trm_fvar x)) (at level 67).


Fixpoint t_close_var_rec (k : nat) (z : var) (t : t_trm) {struct t} : t_trm :=
  match t with
  | t_trm_bvar i => t
  | t_trm_fvar x => if var_compare x z then (t_trm_bvar k) else t
  | t_trm_abs ts => let t_close_var_rec_S := (t_close_var_rec (S k) z) in
                  t_trm_abs (map t_close_var_rec_S ts)
  | t_trm_app t1 t2 => t_trm_app (t_close_var_rec k z t1) (t_close_var_rec k z t2)
  | t_trm_setcar p v => t_trm_setcar (t_close_var_rec k z p) (t_close_var_rec k z v)
  | t_trm_setcdr p v => t_trm_setcdr (t_close_var_rec k z p) (t_close_var_rec k z v)
  | t_trm_cons v1 v2 => t_trm_cons (t_close_var_rec k z v1) (t_close_var_rec k z v2)
  | t_trm_car p => t_trm_car (t_close_var_rec k z p)
  | t_trm_cdr p => t_trm_cdr (t_close_var_rec k z p)
  | t_trm_begin ts => t_trm_begin (map (t_close_var_rec k z) ts)
  | _ => t
  end.


Definition t_close_var z t := t_close_var_rec 0 z t.

Fixpoint t_open_each ts x :=
  match ts with
  | [] => []
  | t :: ts' => (t ^t x) :: t_open_each ts' x
  end.

Fixpoint t_open_each_term ts u :=
  match ts with
  | [] => []
  | t :: ts' => (t ^^s u) :: t_open_each_term ts' u
  end.

Inductive t_term : t_trm -> Prop :=
  | t_term_fvar : forall x,
      t_term (t_trm_fvar x)
  | t_term_app : forall t1 t2,
      t_term t1 -> t_term t2 -> t_term (t_trm_app t1 t2)
  | t_term_abs : forall L ts,
      (forall x, x \notin L -> t_terms (t_open_each ts x)) ->
      t_term (t_trm_abs ts)
  | t_term_begin : forall L ts,
      (forall x, x \notin L -> t_terms (t_open_each ts x)) ->
      t_term (t_trm_begin ts)
  | t_term_let : forall L ts t b,
      t_term b ->
      In t ts ->
      (forall x, x \notin L -> t_terms (t_open_each ts x)) ->
      t_term (t_trm_let b ts)
  | t_term_setcar : forall p v,
      t_term p -> t_term v -> t_term (t_trm_setcar p v)
  | t_term_setcdr : forall p v,
      t_term p -> t_term v -> t_term (t_trm_setcdr p v)
  | t_term_cons : forall v1 v2, 
      t_term v1 -> t_term v2 -> t_term (t_trm_cons v1 v2)
  | t_term_car : forall p,
      t_term p -> t_term (t_trm_car p)
  | t_term_cdr : forall p,
      t_term p -> t_term (t_trm_cdr p)
  | t_term_pp : forall n,
      t_term (t_trm_pp n)
  | t_term_num : forall i,
      t_term (t_trm_num i)
  | t_term_null : t_term (t_trm_null)
  | t_term_true : t_term (t_trm_true)
  | t_term_false : t_term (t_trm_false)

with t_terms : list t_trm -> Prop :=
  | t_terms_nil : t_terms ([])
  | t_terms_single : forall t, t_term t -> t_terms [t]
  | t_terms_next : 
      forall t ts,
        t_terms ts -> 
        t_term t ->
        t_terms (t :: ts).

Definition t_body ts :=
  exists L,
  forall x, x \notin L -> t_terms (t_open_each ts x).

Fixpoint t_fv (t : t_trm) : vars :=
  let fix fvs' (ts : list t_trm) : vars :=
    match ts with
    | [] => \{}
    | t :: ts' => t_fv t \u fvs' ts'
    end
  in
    match t with
    | t_trm_fvar y => \{y}
    | t_trm_bvar _ => \{}
    | t_trm_abs ts => fvs' ts
    | t_trm_begin ts => fvs' ts
    | t_trm_app t1 t2 => (t_fv t1) \u (t_fv t2)
    | t_trm_set_top x t1 => \{x} \u (t_fv t1)
    | t_trm_setcar p v => (t_fv p) \u (t_fv v)
    | t_trm_setcdr p v => (t_fv p) \u (t_fv v)
    | t_trm_cons v1 v2 => (t_fv v1) \u (t_fv v2)
    | t_trm_car p => t_fv p
    | t_trm_cdr p => t_fv p
    | _ => \{}
    end.

Fixpoint t_subst (z : var) (u : t_trm) (t : t_trm) {struct t} : t_trm :=
  let fix substs (ts : list t_trm) :=
    match ts with
    | [] => []
    | t' :: ts' => (t_subst z u t') :: (substs ts')
    end
  in
  match t with
  | t_trm_abs ts => t_trm_abs (substs ts)
  | t_trm_begin ts => t_trm_begin (substs ts)
  | t_trm_app t1 t2 => t_trm_app (t_subst z u t1) (t_subst z u t2)
  | t_trm_let v ts => t_trm_let (t_subst z u v) (substs ts)
  | t_trm_setcar p v => t_trm_setcar (t_subst z u p) (t_subst z u v)
  | t_trm_setcdr p v => t_trm_setcdr (t_subst z u p) (t_subst z u v)
  | t_trm_cons v1 v2 => t_trm_cons (t_subst z u v1) (t_subst z u v2)
  | t_trm_car p => t_trm_car (t_subst z u p)
  | t_trm_cdr p => t_trm_cdr (t_subst z u p)
  | t_trm_fvar x => if (var_compare x z) then u else t
  | t_trm_bvar i => t
  | _ => t
  end.

Notation "[ z ~>t u ] t" := (t_subst z u t) (at level 68).

Fixpoint t_trm_size (t : t_trm) {struct t} : nat :=
  match t with 
  | t_trm_abs ts => 1 + (sum (map t_trm_size ts))
  | t_trm_begin ts => 1 + (sum (map t_trm_size ts))
  | t_trm_app t1 t2 => 1 + (t_trm_size t1) + (t_trm_size t2)
  | t_trm_set_top x t1 => 2 + (t_trm_size t1)
  | t_trm_let v ts => 1 + (t_trm_size v) + (sum (map t_trm_size ts))
  | t_trm_setcar p v => 1 + (t_trm_size p) + (t_trm_size v)
  | t_trm_setcdr p v => 1 + (t_trm_size p) + (t_trm_size v)
  | t_trm_cons v1 v2 => 1 + (t_trm_size v1) + (t_trm_size v2)
  | t_trm_car p => 1 + (t_trm_size p)
  | t_trm_cdr p => 1 + (t_trm_size p)
  | t_trm_fvar _ => 1
  | t_trm_bvar _ => 1
  | _ => 1
  end.

*)