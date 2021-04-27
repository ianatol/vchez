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
                      | (s_trm_var (bvar n)) => if (i =? n) then SomeE true else has_assigning_set n' i t1
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
                            if (a =? i)
                            then SomeE ` (s_trm_setcar ; x ; t1') 
                            else SomeE (s_trm_set x t1')
                        | _ => SomeE (s_trm_set x t1')
                        end
          
    | s_trm_var v => match v with
                     | bvar a => if (a =? i)
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