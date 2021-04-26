From vchez Require Import Definitions.
From vchez Require Import Helpers.
From Coq Require Import Strings.String.
From Coq Require Import List.
Import ListNotations.
Import Nat.

(* reworking pass with new definitions
(* 
Defines the np-convert-assignments pass, which converts s_trm to t_trm,
as well as a pass that desugars t_trm by converting lets into lambda applications
*)

Definition orb_e t1 t2 :=
  ' c1 <- t1 ;; ' c2 <- t2 ;; SomeE (orb c1 c2).

Fixpoint has_assigning_set (n i : nat) (t : s_trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' => 
    match t with
    | s_trm_abs ts => has_assigning_set_list n' (S i) ts
    | s_trm_app t1 t2 => orb_e (has_assigning_set n' i t1) (has_assigning_set n' i t2)
    | s_trm_set x t1 => match x with
                      | (s_trm_bvar n) => if (i =? n) then SomeE true else has_assigning_set n' i t1
                      | _ => has_assigning_set n' i t1
                      end
    | s_trm_setcar p v => orb_e (has_assigning_set n' i p) (has_assigning_set n' i v)
    | s_trm_setcdr p v => orb_e (has_assigning_set n' i p) (has_assigning_set n' i v)
    | s_trm_cons v1 v2 => orb_e (has_assigning_set n' i v1) (has_assigning_set n' i v2)
    | s_trm_car p => (has_assigning_set n' i p)
    | s_trm_cdr p => (has_assigning_set n' i p)
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

Fixpoint handle_assigning_set (n i : nat) (t : s_trm) :=
  match n with 
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    | s_trm_abs ts =>     ' ts' <- (handle_assigning_set_list n' (S i) ts) ;; 
                          SomeE (s_trm_abs ts')
    | s_trm_bvar n =>     if (i =? n) then SomeE (s_trm_car (s_trm_bvar n)) else SomeE (s_trm_bvar n)
    | s_trm_set x t1 =>   ' t1' <- (handle_assigning_set n' i t1) ;;
                        match x with
                        | s_trm_bvar n => if (i =? n) then SomeE (s_trm_setcar x t1') else SomeE (s_trm_set x t1')
                        | _ => SomeE (s_trm_set x t1')
                        end
    | s_trm_app t1 t2 =>  ' t1' <- (handle_assigning_set n' i t1) ;;
                        ' t2' <- (handle_assigning_set n' i t2) ;;
                        SomeE (s_trm_app t1' t2')
    | s_trm_setcar p v => ' p' <- (handle_assigning_set n' i p) ;;
                        ' v' <- (handle_assigning_set n' i v) ;;
                        SomeE (s_trm_setcar p' v')
    | s_trm_setcdr p v => ' p' <- (handle_assigning_set n' i p) ;;
                        ' v' <- (handle_assigning_set n' i v) ;;
                        SomeE (s_trm_setcdr p' v')
    | s_trm_cons v1 v2 => ' v1' <- (handle_assigning_set n' i v1) ;;
                        ' v2' <- (handle_assigning_set n' i v2) ;;
                        SomeE (s_trm_cons v1' v2')
    | s_trm_car p =>      ' p' <- (handle_assigning_set n' i p) ;;
                        SomeE (s_trm_car p')
    | s_trm_cdr p =>      ' p' <- (handle_assigning_set n' i p) ;;
                        SomeE (s_trm_cdr p')
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

Fixpoint convert_assignments (n : nat) (t : s_trm) : OptionE t_trm :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    | s_trm_abs ts => ' ts_has_set <- (has_sets_list ts) ;;
                      if ts_has_set then
                        ' body <- handle_sets_list ts ;;
                        ' body' <- convert_assignments_list n' body ;;
                        SomeE (t_trm_abs 
                                [t_trm_let (t_trm_cons (t_trm_bvar 0) (t_trm_null))
                                  body'])
                      else
                        ' body <- convert_assignments_list n' ts ;;
                        SomeE (t_trm_abs body)
    | s_trm_app t1 t2 => ' t1' <- (convert_assignments n' t1) ;;
                         ' t2' <- (convert_assignments n' t2) ;;
                         SomeE (t_trm_app t1' t2')
    | s_trm_begin ts =>  ' ts' <- (convert_assignments_list n' ts) ;;
                         SomeE (t_trm_begin ts')
    | s_trm_set x t1 => ' t1' <- (convert_assignments n' t1) ;;
                          match x with 
                          | s_trm_fvar y => SomeE (t_trm_set_top y t1')
                          | _ => NoneE "Set applied to invalid bound variable"
                          end
    | s_trm_setcar p v => ' p' <- (convert_assignments n' p) ;;
                          ' v' <- (convert_assignments n' v) ;;
                          SomeE (t_trm_setcar p' v')
    | s_trm_setcdr p v => ' p' <- (convert_assignments n' p) ;;
                          ' v' <- (convert_assignments n' v) ;;
                          SomeE (t_trm_setcdr p' v')
    | s_trm_cons v1 v2 => ' v1' <- (convert_assignments n' v1) ;;
                          ' v2' <- (convert_assignments n' v2) ;;
                          SomeE (t_trm_cons v1' v2')
    | s_trm_car p =>      ' p' <- (convert_assignments n' p) ;;
                          SomeE (t_trm_car p')
    | s_trm_cdr p =>      ' p' <- (convert_assignments n' p) ;;
                          SomeE (t_trm_cdr p')
    | s_trm_bvar i => SomeE (t_trm_bvar i)
    | s_trm_fvar x => SomeE (t_trm_fvar x)
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

(*changes let v ts into app (abs ts) v
  also changes set top into setting a free variable *)
Fixpoint de_sugar n t :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match t with
    | t_trm_abs ts =>      ' ts' <- de_sugar_list n' ts ;;
                           SomeE (s_trm_abs ts')
    | t_trm_app t1 t2 =>   ' t1' <- de_sugar n' t1 ;;
                           ' t2' <- de_sugar n' t2 ;;
                           SomeE (s_trm_app t1' t2')
    | t_trm_let v ts =>    ' v' <- de_sugar n' v ;;
                           ' ts' <- de_sugar_list n' ts ;;
                           SomeE (s_trm_app (s_trm_abs ts') v')
    | t_trm_set_top x v => ' v' <- de_sugar n' v ;;
                            SomeE (s_trm_set (s_trm_fvar x) v')
    | t_trm_begin ts =>    ' ts' <- de_sugar_list n' ts ;;
                           SomeE (s_trm_begin ts')
    | t_trm_setcar p v =>  ' p' <- de_sugar n' p ;;
                           ' v' <- de_sugar n' v ;;
                           SomeE (s_trm_setcar p' v')
    | t_trm_setcdr p v =>  ' p' <- de_sugar n' p ;;
                           ' v' <- de_sugar n' v ;;
                           SomeE (s_trm_setcdr p' v')
    | t_trm_cons v1 v2 =>  ' v1' <- de_sugar n' v1 ;;
                           ' v2' <- de_sugar n' v2 ;;
                           SomeE (s_trm_cons v1' v2')
    | t_trm_car p =>       ' p' <- de_sugar n' p ;;
                           SomeE (s_trm_car p')
    | t_trm_cdr p =>       ' p' <- de_sugar n' p ;;
                           SomeE (s_trm_cdr p')
    | t_trm_bvar i => SomeE (s_trm_bvar i)
    | t_trm_fvar x => SomeE (s_trm_fvar x)
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
*)