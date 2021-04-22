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
Inductive trm : Set :=
  | trm_let (v : trm)(ts : list trm)
  | trm_abs  (ts : list trm)
  | trm_app  (t1 : trm)(t2 : trm)
  | trm_set (x : trm)(t : trm)
  | trm_setcar (pair : trm)(v : trm)
  | trm_setcdr (pair : trm)(v : trm)
  | trm_cons (v1 : trm)(v2 : trm)
  | trm_car (pair : trm)
  | trm_cdr (pair : trm)
  | trm_bvar (i : nat)
  | trm_fvar (x : var)
  | trm_pp (n : var)
  | trm_num (i : nat)
  | trm_null
  | trm_true
  | trm_false
  (*
  | pre_begin (e : trm)(es : list trm)
  | pre_begin0 (e : trm)(es : list trm)
  *).

Inductive value : trm -> Prop :=
  | value_abs : forall ts,
      value (trm_abs ts)
  | value_pp : forall n,
      value (trm_pp n)
  | value_num : forall i,
      value (trm_num i)
  | value_null : value (trm_null)
  | value_true : value (trm_true)
  | value_false : value (trm_false).

(* 
Opening a term t with a term u containing a fresh free variable x.
  so u = (trm_var (fvar x))
To do so, we replace all references to local bvar with u.
This means we have to keep track of the current level of abstraction with k
So we are replacing all (bvar k) with (fvar x), and incrementing k with abstraction levels
*)

Fixpoint open_rec (k : nat) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i => if (k =? i) then u else t
  | trm_fvar x => t
  | trm_abs ts => let open_rec_S := (open_rec (S k) u) in
                  trm_abs (map open_rec_S ts)
  | trm_let b ts => let open_rec_S := (open_rec (S k) u) in
                    trm_let (open_rec k u b) (map open_rec_S ts)
  | trm_app t1 t2 => trm_app (open_rec k u t1)(open_rec k u t2)
  | trm_set x t1 => trm_set (open_rec k u x) (open_rec k u t1)
  | trm_setcar p v => trm_setcar (open_rec k u p) (open_rec k u v)
  | trm_setcdr p v => trm_setcdr (open_rec k u p) (open_rec k u v)
  | trm_cons v1 v2 => trm_cons (open_rec k u v1)(open_rec k u v2)
  | trm_car p => trm_car (open_rec k u p)
  | trm_cdr p => trm_cdr (open_rec k u p)
  | _ => t
  end.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).

Definition open t u := open_rec 0 u t.

Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (trm_fvar x)).

(*
Closing a term is the inverse of opening.
Replaces a free var z with bvar n where n is the current level of abstraction
*)
Fixpoint close_var_rec (k : nat) (z : var) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i => t
  | trm_fvar x => if var_compare x z then (trm_bvar k) else t
  | trm_abs ts => let close_var_rec_S := (close_var_rec (S k) z) in
                  trm_abs (map close_var_rec_S ts)
  | trm_let b ts => let close_var_rec_S := (close_var_rec (S k) z) in
                    trm_let (close_var_rec k z b) (map close_var_rec_S ts)
  | trm_app t1 t2 => trm_app (close_var_rec k z t1) (close_var_rec k z t2)
  | trm_set x t1 => trm_set (close_var_rec k z x) (close_var_rec k z t1)
  | trm_setcar p v => trm_setcar (close_var_rec k z p) (close_var_rec k z v)
  | trm_setcdr p v => trm_setcdr (close_var_rec k z p) (close_var_rec k z v)
  | trm_cons v1 v2 => trm_cons (close_var_rec k z v1) (close_var_rec k z v2)
  | trm_car p => trm_car (close_var_rec k z p)
  | trm_cdr p => trm_cdr (close_var_rec k z p)
  | _ => t
  end.

Definition close_var z t := close_var_rec 0 z t.
Fixpoint open_each ts x :=
  match ts with
  | [] => []
  | t :: ts' => (t ^ x) :: open_each ts' x
  end.

Fixpoint open_each_term ts u :=
  match ts with
  | [] => []
  | t :: ts' => (t ^^ u) :: open_each_term ts' u
  end.
  


Inductive term : trm -> Prop :=
  | term_fvar : forall x,
      term (trm_fvar x)
  | term_app : forall t1 t2,
      term t1 -> term t2 -> term (trm_app t1 t2)
  | term_abs : forall L ts,
      (forall x, x \notin L -> terms (open_each ts x)) ->
      term (trm_abs ts)
      (* (forall x, x \notin L -> term (t ^ x)) ->
      term (trm_abs ts) *)
  | term_let : forall L ts t b,
      term b ->
      In t ts ->
      (forall x, x \notin L -> terms (open_each ts x)) ->
      term (trm_let b ts)
  | term_set : forall b t,
      term b -> term t -> term (trm_set b t)
  | term_setcar : forall p v,
      term p -> term v -> term (trm_setcar p v)
  | term_setcdr : forall p v,
      term p -> term v -> term (trm_setcdr p v)
  | term_cons : forall v1 v2, 
      term v1 -> term v2 -> term (trm_cons v1 v2)
  | term_car : forall p,
      term p -> term (trm_car p)
  | term_cdr : forall p,
      term p -> term (trm_cdr p)
  | term_pp : forall n,
      term (trm_pp n)
  | term_num : forall i,
      term (trm_num i)
  | term_null : term (trm_null)
  | term_true : term (trm_true)
  | term_false : term (trm_false)

with terms : list trm -> Prop :=
  | terms_nil : terms ([])
  | terms_single : forall t, term t -> terms [t]
  | terms_next : 
      forall t ts,
        terms ts -> 
        term t ->
        terms (t :: ts).
                 



(* Body of an abstraction *)
Definition body ts :=
  exists L,
  forall x, x \notin L -> terms (open_each ts x).

Fixpoint big_unionf (ts : list trm) (f : trm -> vars) : vars :=
  match ts with
  | [] => \{}
  | t :: ts' => f t \u big_unionf ts' f
  end.

(* Free variables of a term *)
Fixpoint fv (t : trm) : vars :=
  let fix fvs' (ts : list trm) : vars :=
    match ts with
    | [] => \{}
    | t :: ts' => fv t \u fvs' ts'
    end
  in
    match t with
    | trm_fvar y => \{y}
    | trm_bvar _ => \{}
    | trm_let b ts => (fv b) \u (fvs' ts) (* @fold_left (vars) (vars) (@union var) (map fv (b :: ts)) \{} *)
    | trm_abs ts => fvs' ts (* @fold_left (vars) (vars) (@union var) (map fv ts) \{} *)
    | trm_app t1 t2 => (fv t1) \u (fv t2)
    | trm_set x t1 => (fv x) \u (fv t1)
    | trm_setcar p v => (fv p) \u (fv v)
    | trm_setcdr p v => (fv p) \u (fv v)
    | trm_cons v1 v2 => (fv v1) \u (fv v2)
    | trm_car p => fv p
    | trm_cdr p => fv p
    | _ => \{}
    end.

Fixpoint fvs (ts : list trm) : vars :=
  match ts with 
  | [] => \{}
  | t :: ts' => fv t \u fvs ts'
  end.

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  let fix substs (ts : list trm) :=
    match ts with
    | [] => []
    | t' :: ts' => (subst z u t') :: (substs ts')
    end
  in
  match t with
  | trm_let v ts => trm_let (subst z u v) (substs ts)
  | trm_abs ts => trm_abs (substs ts)
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_set x t1 => trm_set (subst z u x) (subst z u t1)
  | trm_setcar p v => trm_setcar (subst z u p) (subst z u v)
  | trm_setcdr p v => trm_setcdr (subst z u p) (subst z u v)
  | trm_cons v1 v2 => trm_cons (subst z u v1) (subst z u v2)
  | trm_car p => trm_car (subst z u p)
  | trm_cdr p => trm_cdr (subst z u p)
  | trm_fvar x => if (var_compare x z) then u else t
  | trm_bvar i => t
  | _ => t
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

(* Definition sum (A : Type) (l : list A) (f : A -> nat) :=
  (fold_left
   (fun a x => a + x)
   0
   (map f l)).
*)

Definition sum (l : list nat) :=
  fold_left (plus) l 0.

Fixpoint trm_size (t : trm) {struct t} : nat :=
  match t with
  | trm_let v ts => 1 + (trm_size v) + (sum (map trm_size ts))
  | trm_abs ts => 1 + (sum (map trm_size ts))
  | trm_app t1 t2 => 1 + (trm_size t1) + (trm_size t2)
  | trm_set x t1 => 1 + (trm_size x) + (trm_size t1)
  | trm_setcar p v => 1 + (trm_size p) + (trm_size v)
  | trm_setcdr p v => 1 + (trm_size p) + (trm_size v)
  | trm_cons v1 v2 => 1 + (trm_size v1) + (trm_size v2)
  | trm_car p => 1 + (trm_size p)
  | trm_cdr p => 1 + (trm_size p)
  | trm_fvar _ => 1
  | trm_bvar _ => 1
  | _ => 1
  end.



