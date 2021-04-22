From Coq Require Import List.
Import ListNotations.
Import Nat.

From TLC Require Export LibFix.
From TLC Require Export LibVar.
From TLC Require Export LibFset.


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

(*source langauge pre-terms*)
Inductive s_trm : Set :=
  | s_trm_abs  (ts : list s_trm)
  | s_trm_app  (t1 : s_trm)(t2 : s_trm)
  | s_trm_begin (ts : list s_trm)
  | s_trm_set (x : s_trm)(t : s_trm)
  | s_trm_setcar (pair : s_trm)(v : s_trm)
  | s_trm_setcdr (pair : s_trm)(v : s_trm)
  | s_trm_cons (v1 : s_trm)(v2 : s_trm)
  | s_trm_car (pair : s_trm)
  | s_trm_cdr (pair : s_trm)
  | s_trm_bvar (i : nat)
  | s_trm_fvar (x : var)
  | s_trm_pp (n : var)
  | s_trm_num (i : nat)
  | s_trm_null
  | s_trm_true
  | s_trm_false.

(* target language pre-terms*)
Inductive t_trm : Set :=
  | t_trm_abs  (ts : list t_trm)
  | t_trm_app  (t1 : t_trm)(t2 : t_trm)
  | t_trm_let (v : t_trm) (ts : list t_trm)
  | t_trm_set_top (x : var) (t : t_trm)
  | t_trm_begin (ts : list t_trm)
  | t_trm_setcar (pair : t_trm)(v : t_trm)
  | t_trm_setcdr (pair : t_trm)(v : t_trm)
  | t_trm_cons (v1 : t_trm)(v2 : t_trm)
  | t_trm_car (pair : t_trm)
  | t_trm_cdr (pair : t_trm)
  | t_trm_bvar (i : nat)
  | t_trm_fvar (x : var)
  | t_trm_pp (n : var)
  | t_trm_num (i : nat)
  | t_trm_null
  | t_trm_true
  | t_trm_false.

Inductive s_val : s_trm -> Prop :=
  | sval_abs : forall ts,
      s_val (s_trm_abs ts)
  | sval_pp : forall n,
      s_val (s_trm_pp n)
  | sval_num : forall i,
      s_val (s_trm_num i)
  | sval_null : s_val (s_trm_null)
  | sval_true : s_val (s_trm_true)
  | sval_false : s_val (s_trm_false).

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

(* 
Opening a term t with a term u containing a fresh free variable x.
  so u = (s_trm_var (fvar x))
To do so, we replace all references to local bvar with u.
This means we have to keep track of the current level of abstraction with k
So we are replacing all (bvar k) with (fvar x), and incrementing k with abstraction levels
*)

Fixpoint s_open_rec (k : nat) (u : s_trm) (t : s_trm) {struct t} : s_trm :=
  match t with
  | s_trm_bvar i => if (k =? i) then u else t
  | s_trm_fvar x => t
  | s_trm_abs ts => let s_open_rec_S := (s_open_rec (S k) u) in
                    s_trm_abs (map s_open_rec_S ts)
  | s_trm_app t1 t2 => s_trm_app (s_open_rec k u t1)(s_open_rec k u t2)
  | s_trm_set x t1 => s_trm_set (s_open_rec k u x) (s_open_rec k u t1)
  | s_trm_setcar p v => s_trm_setcar (s_open_rec k u p) (s_open_rec k u v)
  | s_trm_setcdr p v => s_trm_setcdr (s_open_rec k u p) (s_open_rec k u v)
  | s_trm_cons v1 v2 => s_trm_cons (s_open_rec k u v1)(s_open_rec k u v2)
  | s_trm_car p => s_trm_car (s_open_rec k u p)
  | s_trm_cdr p => s_trm_cdr (s_open_rec k u p)
  | s_trm_begin ts => let s_open_rec_S := (s_open_rec (S k) u) in
                      s_trm_begin (map s_open_rec_S ts)
  | _ => t
  end.

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

Notation "{ k ~>s u } t" := (s_open_rec k u t) (at level 67).
Notation "{ k ~>t u } t" := (t_open_rec k u t) (at level 67).

Definition s_open t u := s_open_rec 0 u t.
Definition t_open t u := t_open_rec 0 u t.

Notation "t ^^s u" := (s_open t u) (at level 67).
Notation "t ^s x" := (s_open t (s_trm_fvar x)) (at level 67).

Notation "t ^^t u" := (t_open t u) (at level 67).
Notation "t ^t x" := (t_open t (t_trm_fvar x)) (at level 67).

(*
Closing a term is the inverse of opening.
Replaces a free var z with bvar n where n is the current level of abstraction
*)
Fixpoint s_close_var_rec (k : nat) (z : var) (t : s_trm) {struct t} : s_trm :=
  match t with
  | s_trm_bvar i => t
  | s_trm_fvar x => if var_compare x z then (s_trm_bvar k) else t
  | s_trm_abs ts => let s_close_var_rec_S := (s_close_var_rec (S k) z) in
                  s_trm_abs (map s_close_var_rec_S ts)
  | s_trm_app t1 t2 => s_trm_app (s_close_var_rec k z t1) (s_close_var_rec k z t2)
  | s_trm_set x t1 => s_trm_set (s_close_var_rec k z x) (s_close_var_rec k z t1)
  | s_trm_setcar p v => s_trm_setcar (s_close_var_rec k z p) (s_close_var_rec k z v)
  | s_trm_setcdr p v => s_trm_setcdr (s_close_var_rec k z p) (s_close_var_rec k z v)
  | s_trm_cons v1 v2 => s_trm_cons (s_close_var_rec k z v1) (s_close_var_rec k z v2)
  | s_trm_car p => s_trm_car (s_close_var_rec k z p)
  | s_trm_cdr p => s_trm_cdr (s_close_var_rec k z p)
  | s_trm_begin ts => s_trm_begin (map (s_close_var_rec k z) ts)
  | _ => t
  end.

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

Definition s_close_var z t := s_close_var_rec 0 z t.
Definition t_close_var z t := t_close_var_rec 0 z t.

Fixpoint s_open_each ts x :=
  match ts with
  | [] => []
  | t :: ts' => (t ^s x) :: s_open_each ts' x
  end.

Fixpoint t_open_each ts x :=
  match ts with
  | [] => []
  | t :: ts' => (t ^t x) :: t_open_each ts' x
  end.

Fixpoint s_open_each_term ts u :=
  match ts with
  | [] => []
  | t :: ts' => (t ^^s u) :: s_open_each_term ts' u
  end.
  
Fixpoint t_open_each_term ts u :=
  match ts with
  | [] => []
  | t :: ts' => (t ^^s u) :: t_open_each_term ts' u
  end.

Inductive s_term : s_trm -> Prop :=
  | s_term_fvar : forall x,
      s_term (s_trm_fvar x)
  | s_term_app : forall t1 t2,
      s_term t1 -> s_term t2 -> s_term (s_trm_app t1 t2)
  | s_term_abs : forall L ts,
      (forall x, x \notin L -> s_terms (s_open_each ts x)) ->
      s_term (s_trm_abs ts)
  | s_term_begin : forall L ts,
      (forall x, x \notin L -> s_terms (s_open_each ts x)) ->
      s_term (s_trm_begin ts)
  | s_term_set : forall b t,
      s_term b -> s_term t -> s_term (s_trm_set b t)
  | s_term_setcar : forall p v,
      s_term p -> s_term v -> s_term (s_trm_setcar p v)
  | s_term_setcdr : forall p v,
      s_term p -> s_term v -> s_term (s_trm_setcdr p v)
  | s_term_cons : forall v1 v2, 
      s_term v1 -> s_term v2 -> s_term (s_trm_cons v1 v2)
  | s_term_car : forall p,
      s_term p -> s_term (s_trm_car p)
  | s_term_cdr : forall p,
      s_term p -> s_term (s_trm_cdr p)
  | s_term_pp : forall n,
      s_term (s_trm_pp n)
  | s_term_num : forall i,
      s_term (s_trm_num i)
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


(* Body of an abstraction *)
Definition s_body ts :=
  exists L,
  forall x, x \notin L -> s_terms (s_open_each ts x).

Definition t_body ts :=
  exists L,
  forall x, x \notin L -> t_terms (t_open_each ts x).

(* Free variables of a source term *)
Fixpoint s_fv (t : s_trm) : vars :=
  let fix fvs' (ts : list s_trm) : vars :=
    match ts with
    | [] => \{}
    | t :: ts' => s_fv t \u fvs' ts'
    end
  in
    match t with
    | s_trm_fvar y => \{y}
    | s_trm_bvar _ => \{}
    | s_trm_abs ts => fvs' ts
    | s_trm_begin ts => fvs' ts
    | s_trm_app t1 t2 => (s_fv t1) \u (s_fv t2)
    | s_trm_set x t1 => (s_fv x) \u (s_fv t1)
    | s_trm_setcar p v => (s_fv p) \u (s_fv v)
    | s_trm_setcdr p v => (s_fv p) \u (s_fv v)
    | s_trm_cons v1 v2 => (s_fv v1) \u (s_fv v2)
    | s_trm_car p => s_fv p
    | s_trm_cdr p => s_fv p
    | _ => \{}
    end.

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

Fixpoint s_subst (z : var) (u : s_trm) (t : s_trm) {struct t} : s_trm :=
  let fix substs (ts : list s_trm) :=
    match ts with
    | [] => []
    | t' :: ts' => (s_subst z u t') :: (substs ts')
    end
  in
  match t with
  | s_trm_abs ts => s_trm_abs (substs ts)
  | s_trm_begin ts => s_trm_begin (substs ts)
  | s_trm_app t1 t2 => s_trm_app (s_subst z u t1) (s_subst z u t2)
  | s_trm_set x t1 => s_trm_set (s_subst z u x) (s_subst z u t1)
  | s_trm_setcar p v => s_trm_setcar (s_subst z u p) (s_subst z u v)
  | s_trm_setcdr p v => s_trm_setcdr (s_subst z u p) (s_subst z u v)
  | s_trm_cons v1 v2 => s_trm_cons (s_subst z u v1) (s_subst z u v2)
  | s_trm_car p => s_trm_car (s_subst z u p)
  | s_trm_cdr p => s_trm_cdr (s_subst z u p)
  | s_trm_fvar x => if (var_compare x z) then u else t
  | s_trm_bvar i => t
  | _ => t
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

Notation "[ z ~>s u ] t" := (s_subst z u t) (at level 68).
Notation "[ z ~>t u ] t" := (t_subst z u t) (at level 68).

Definition sum (l : list nat) :=
  fold_left (plus) l 0.

Fixpoint s_trm_size (t : s_trm) {struct t} : nat :=
  match t with
  | s_trm_abs ts => 1 + (sum (map s_trm_size ts))
  | s_trm_begin ts => 1 + (sum (map s_trm_size ts))
  | s_trm_app t1 t2 => 1 + (s_trm_size t1) + (s_trm_size t2)
  | s_trm_set x t1 => 1 + (s_trm_size x) + (s_trm_size t1)
  | s_trm_setcar p v => 1 + (s_trm_size p) + (s_trm_size v)
  | s_trm_setcdr p v => 1 + (s_trm_size p) + (s_trm_size v)
  | s_trm_cons v1 v2 => 1 + (s_trm_size v1) + (s_trm_size v2)
  | s_trm_car p => 1 + (s_trm_size p)
  | s_trm_cdr p => 1 + (s_trm_size p)
  | s_trm_fvar _ => 1
  | s_trm_bvar _ => 1
  | _ => 1
  end.

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


