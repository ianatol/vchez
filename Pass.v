From vchez Require Import Definitions.
From vchez Require Import Helpers.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
Import Nat.

(* 
Defines the np-convert-assignments pass, which converts s_trm to t_trm,
as well as a pass that desugars t_trm by converting lets into lambda applications
*)

Definition orb_e t1 t2 :=
  ' c1 <- t1 ;; ' c2 <- t2 ;; SomeE (orb c1 c2).


(* determine if a term has a set! targetting a bound variable *)
Fixpoint has_assigning_set (n i : nat) (t : s_trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' => 
    match t with
    | s_trm_seq ts => has_assigning_set_list n' i ts
    | s_trm_begin ts => has_assigning_set_list n' i ts
    | s_trm_abs ts => has_assigning_set_list n' (S i) ts
    | s_trm_set x t1 => match x with
                      | (s_trm_var (bvar n)) => if (i == n) then SomeE true else has_assigning_set n' i t1
                      | _ => has_assigning_set n' i t1
                      end
    | _ => SomeE false
    end
  end

with has_assigning_set_list (n i : nat) (ts : list s_trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' => 
    match ts with 
    | nil => SomeE false
    | t :: ts' => orb_e (has_assigning_set n' i t) (has_assigning_set_list n' i ts')
    end
  end.

(* converts 
   set! to set-car! and (bvar i) to (car (bvar i))
   in abstractions that convert-assignments applies to *)
Fixpoint handle_assigning_set (n i : nat) (t : s_trm) :=
  (* step indexed to promise termination to Coq *)
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    (* do not increment i, since seq and begin don't abstract *)
    | s_trm_seq ts =>   ' ts' <- (handle_assigning_set_list n' i ts) ;;
                        SomeE (s_trm_seq ts')
    | s_trm_begin ts => ' ts' <- (handle_assigning_set_list n' i ts) ;;
                        SomeE (s_trm_begin ts')

    (* increment i and apply to body of abstraction to find nested references *)
    | s_trm_abs ts =>   ' ts' <- (handle_assigning_set_list n' (S i) ts) ;; 
                        SomeE (s_trm_abs ts')

    (* if set is assigning to a bvar at our current depth, replace it with setcar *)
    | s_trm_set x t1 => ' t1' <- (handle_assigning_set n' i t1) ;;
                        match x with
                        | (s_trm_var (bvar a)) => 
                            if (a == i)
                            then SomeE ` (s_trm_setcar ; x ; t1') 
                            else SomeE (s_trm_set x t1')
                        | _ => SomeE (s_trm_set x t1')
                        end
          
    | s_trm_var v => match v with
                     | bvar a => if (a == i)
                                 then SomeE ` (s_trm_car ; (s_trm_var (bvar a)))
                                 else SomeE t
                     | fvar _ => SomeE t
                     end
    | t => SomeE t
    end
  end

with handle_assigning_set_list (n i : nat) (ts : list s_trm) :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match ts with
    | nil => SomeE nil
    | t' :: ts' => ' e_t <- (handle_assigning_set n' i t') ;;
                   ' e_ts <- (handle_assigning_set_list n' i ts') ;;
                   SomeE(e_t :: e_ts)
    end
  end.

Definition big_num := 1000.
Definition handle_sets := handle_assigning_set big_num 0.
Definition handle_sets_list := handle_assigning_set_list big_num 0.
Definition has_sets := has_assigning_set big_num 0.
Definition has_sets_list := has_assigning_set_list big_num 0.

(* target language terms
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
   
 


(* 
converts source to target langauge by:
  looking for abstractions with set! in their body that modify their bound variables 
  and converting them (see Examples.v)
*)
Fixpoint convert_assignments (n : nat) (t : s_trm) : OptionE t_trm :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    (* determine if there is an assigning set! in its body
       if so, perform conversion
       if not, just check for other abstraction/assignments in its body *)
    | s_trm_abs ts => ' ts_has_set <- (has_sets_list ts) ;;
                      if ts_has_set then
                        ' body <- handle_sets_list ts ;;
                        ' body' <- convert_assignments_list n' body ;;
                        SomeE (t_trm_abs 
                                [t_trm_let ${t_trm_cons ; (t_trm_var (bvar 0)) ; t_trm_null}
                                  body'])
                      else
                        ' body <- convert_assignments_list n' ts ;;
                        SomeE (t_trm_abs body)

    (*since seq and begin don't abstract, just look in their body for convertible terms *)
    | s_trm_seq ts =>       ' ts' <- (convert_assignments_list n' ts) ;; 
                         SomeE (t_trm_seq ts')
    | s_trm_begin ts =>  ' ts' <- (convert_assignments_list n' ts) ;;
                         SomeE (t_trm_begin ts')

    (* these are fvar set!, since ones inside abstractions will have been converted to set-car already *)
    | s_trm_set x t1 => ' t1' <- (convert_assignments n' t1) ;;
                          match x with 
                          | (s_trm_var (fvar y)) => SomeE (t_trm_set_top (t_trm_var (fvar y)) t1')
                          | _ => NoneE "Set applied to invalid bound variable"
                          end
    | s_trm_setcar => SomeE t_trm_setcar
    | s_trm_setcdr => SomeE t_trm_setcdr
    | s_trm_cons => SomeE t_trm_cons
    | s_trm_car => SomeE t_trm_car
    | s_trm_cdr => SomeE t_trm_cdr
    | s_trm_var v => SomeE (t_trm_var v)
    | s_trm_pp i => SomeE (t_trm_pp i)
    | s_trm_num i => SomeE (t_trm_num i)
    | s_trm_null => SomeE t_trm_null
    | s_trm_true => SomeE t_trm_true
    | s_trm_false => SomeE t_trm_false
    end
  end
with convert_assignments_list (n : nat) (ts : list s_trm) :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match ts with
    | nil => SomeE nil
    | t :: ts' => ' e_t <- (convert_assignments n' t) ;;
                  ' e_ts <- (convert_assignments_list n' ts') ;;
                  SomeE (e_t :: e_ts)
    end
  end.

(* 
desugars target language back into source language by:
  changing (let v ts) into ((abs ts) v)
  changing (set_top y v) into (set (fvar y) v) *)
Fixpoint de_sugar n t :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    (* change let to abs next to value (application)*)
    | t_trm_let v ts =>    ' v' <- de_sugar n' v ;;
                           ' ts' <- de_sugar_list n' ts ;;
                           SomeE ` ((s_trm_abs ts') ; v')

    (* set_top must be targetting a fvar, so convert it back to set! on a fvar *)
    | t_trm_set_top x v => ' v' <- de_sugar n' v ;;
                           ' x' <- de_sugar n' x ;;
                           match x' with
                           | (s_trm_var (fvar y)) => SomeE (s_trm_set (s_trm_var (fvar y)) v')
                           | _ => NoneE "set_top with invalid target"
                           end

    (* everything else just converts 1-1, while recursing on bodies *)
    | t_trm_abs ts =>      ' ts' <- de_sugar_list n' ts ;;
                           SomeE (s_trm_abs ts')
    | t_trm_seq ts =>      ' ts' <- de_sugar_list n' ts ;;
                           SomeE (s_trm_seq ts')
    | t_trm_begin ts =>    ' ts' <- de_sugar_list n' ts ;;
                           SomeE (s_trm_begin ts')
    | t_trm_var v => SomeE (s_trm_var v)
    | t_trm_setcar => SomeE s_trm_setcar
    | t_trm_setcdr => SomeE s_trm_setcdr
    | t_trm_cons => SomeE s_trm_cons
    | t_trm_car => SomeE s_trm_car
    | t_trm_cdr => SomeE s_trm_cdr
    | t_trm_pp n => SomeE (s_trm_pp n)
    | t_trm_num i => SomeE (s_trm_num i)
    | t_trm_null => SomeE s_trm_null
    | t_trm_true => SomeE s_trm_true
    | t_trm_false => SomeE s_trm_false
    end
  end
with de_sugar_list n ts :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' => 
    match ts with 
    | nil => SomeE nil
    | t :: ts' => ' t' <- de_sugar n' t ;;
                  ' ts'' <- de_sugar_list n' ts' ;;
                  SomeE (t' :: ts'')
    end
  end.

Definition ca t :=
  convert_assignments big_num t.

Definition desugar t :=
  de_sugar big_num t.



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