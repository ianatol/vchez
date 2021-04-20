From vchez Require Import Definitions.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
Import Nat.

(* 
convert_assignments
has-assigning-set
handle-assigning-set
*)

Inductive OptionE (X : Type) : Type :=
  | SomeE (x : X)
  | NoneE (s : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

Notation "' p <- e1 ;; e2"
   := (match e1 with
       | SomeE p => e2
       | NoneE err => NoneE err
       end)
   (right associativity, p pattern, at level 60, e1 at next level).



Definition orb_e t1 t2 :=
  ' c1 <- t1 ;; ' c2 <- t2 ;; SomeE (orb c1 c2).

Fixpoint has_assigning_set (n : nat) (i : nat) (t : trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' => 
    match t with
    | trm_let v ts => has_assigning_set_list n' (S i) ts
    | trm_abs ts => has_assigning_set_list n' (S i) ts
    | trm_app t1 t2 => orb_e (has_assigning_set n' i t1) (has_assigning_set n' i t2)
    | trm_set x t1 => match x with
                      | (trm_bvar n) => if (i =? n) then SomeE true else has_assigning_set n' i t1
                      | _ => has_assigning_set n' i t1
                      end
    | trm_setcar p v => orb_e (has_assigning_set n' i p) (has_assigning_set n' i v)
    | trm_setcdr p v => orb_e (has_assigning_set n' i p) (has_assigning_set n' i v)
    | trm_cons v1 v2 => orb_e (has_assigning_set n' i v1) (has_assigning_set n' i v2)
    | trm_car p => (has_assigning_set n' i p)
    | trm_cdr p => (has_assigning_set n' i p)
    | _ => SomeE false
    end
  end

with has_assigning_set_list (n : nat)(i : nat) (ts : list trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' => 
    match ts with 
    | nil => SomeE false
    | t :: ts' => orb_e (has_assigning_set n' i t) (has_assigning_set_list n' i ts')
    end
  end.

Fixpoint handle_assigning_set (n i : nat) (t : trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    | trm_let v ts =>   ' ts' <- (handle_assigning_set_list n' (S i) ts) ;; SomeE (trm_let v ts')
    | trm_abs ts =>     ' ts' <- (handle_assigning_set_list n' (S i) ts) ;; SomeE (trm_abs ts')
    | trm_bvar n =>     if (i =? n) then SomeE (trm_car (trm_bvar n)) else SomeE (trm_bvar n)
    | trm_set x t1 =>   ' t1' <- (handle_assigning_set n' i t1) ;;
                        ' x' <-  (handle_assigning_set n' i x) ;;
                        match x with
                        | trm_bvar n => if (i =? n) then SomeE (trm_setcar x t1') else SomeE (trm_set x t1')
                        | _ => SomeE (trm_set x' t1')
                        end
    | trm_app t1 t2 =>  ' t1' <- (handle_assigning_set n' i t1) ;;
                        ' t2' <- (handle_assigning_set n' i t2) ;;
                        SomeE (trm_app t1' t2')
    | trm_setcar p v => ' p' <- (handle_assigning_set n' i p) ;;
                        ' v' <- (handle_assigning_set n' i v) ;;
                        SomeE (trm_setcar p' v')
    | trm_setcdr p v => ' p' <- (handle_assigning_set n' i p) ;;
                        ' v' <- (handle_assigning_set n' i v) ;;
                        SomeE (trm_setcdr p' v')
    | trm_cons v1 v2 => ' v1' <- (handle_assigning_set n' i v1) ;;
                        ' v2' <- (handle_assigning_set n' i v2) ;;
                        SomeE (trm_cons v1' v2')
    | trm_car p =>      ' p' <- (handle_assigning_set n' i p) ;;
                        SomeE (trm_car p')
    | trm_cdr p =>      ' p' <- (handle_assigning_set n' i p) ;;
                        SomeE (trm_cdr p')
    | t => SomeE t
    end
  end

with handle_assigning_set_list (n i : nat) (ts : list trm) :=
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

(*
Fixpoint convert_assignments (n : nat) (t : trm) :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    | trm_let v ts => let body := (handle_sets_list ts) in
                        match body with
                        | NoneE s => s
                        | SomeE b => 
                      let body' := (convert_assignments_list n' b) in
                      match body' with
                      | NoneE s => s
                      | SomeE body'' =>
                        if (has_sets_list ts) then
                        SomeE (trm_let v 
                                [trm_let (trm_cons (trm_bvar 0) (trm_null)) body''])
                        else
                        SomeE (trm_let v body')
                      end
    | _ => NoneE "test"
    end
  end
with convert_assignments_list (n : nat) (ts : list trm) :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match ts with
    | nil => SomeE nil
    | t :: ts' => let e_t := (convert_assignments n' t) in
                  let e_ts := (convert_assignments_list n' ts) in
                  match e_t, e_ts with
                  | SomeE t', SomeE ts' => SomeE (t' :: ts')
                  | NoneE s, _ => NoneE s
                  | _, NoneE s => NoneE s
                  end
    end
  end.
*)