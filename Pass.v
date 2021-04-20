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

Definition orb_e (t1 : OptionE bool) (t2 : OptionE bool) : OptionE bool :=
  match t1 with 
  | SomeE c1 => match t2 with
               | SomeE c2 => SomeE (orb c1 c2)
               | NoneE s => NoneE s
                end
  | NoneE s => NoneE s
  end.

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
    | trm_let v ts => match (handle_assigning_set_list n' (S i) ts) with
                      | SomeE ts' => SomeE (trm_let v ts')
                      | NoneE s => NoneE s
                      end
    | trm_abs ts => match (handle_assigning_set_list n' (S i) ts) with
                    | SomeE ts' => SomeE (trm_abs ts')
                    | NoneE s => NoneE s
                    end
    | trm_bvar n => if (i =? n) then SomeE (trm_car (trm_bvar n)) else SomeE (trm_bvar n)
    | trm_set x t1 => let e_t1 := (handle_assigning_set n' i t1) in
                      let e_x := (handle_assigning_set n' i x) in
                      match x with
                      | (trm_bvar n') => match e_t1 with
                                        | SomeE t1' =>  if (i =? n') then SomeE (trm_setcar x t1') else SomeE (trm_set x t1')
                                        | NoneE s => NoneE s
                                        end
                      | _ => match e_t1, e_x with
                             | SomeE t1', SomeE x' => SomeE (trm_set x' t1')
                             | NoneE s, _ => NoneE s
                             | _, NoneE s => NoneE s
                             end 
                      end
    | trm_app t1 t2 => let e_t1 := (handle_assigning_set n' i t1) in
                       let e_t2 := (handle_assigning_set n' i t2) in
                       match e_t1, e_t2 with
                       | SomeE t1', SomeE t2' => SomeE (trm_app t1' t2')
                       | NoneE s, _ => NoneE s
                       | _, NoneE s => NoneE s
                       end
    | trm_setcar p v => let e_p := (handle_assigning_set n' i p) in
                        let e_v := (handle_assigning_set n' i v) in
                        match e_p, e_v with
                        | SomeE p', SomeE v' => SomeE (trm_setcar p' v')
                        | NoneE s, _ => NoneE s
                        | _, NoneE s => NoneE s
                        end
    | trm_setcdr p v => let e_p := (handle_assigning_set n' i p) in
                        let e_v := (handle_assigning_set n' i v) in
                        match e_p, e_v with
                        | SomeE p', SomeE v' => SomeE (trm_setcdr p' v')
                        | NoneE s, _ => NoneE s
                        | _, NoneE s => NoneE s
                        end
    | trm_cons v1 v2 => let e_v1 := (handle_assigning_set n' i v1) in
                        let e_v2 := (handle_assigning_set n' i v2) in
                        match e_v1, e_v2 with
                        | SomeE v1', SomeE v2' => SomeE (trm_cons v1' v2')
                        | NoneE s, _ => NoneE s
                        | _, NoneE s => NoneE s
                        end
    | trm_car p => match (handle_assigning_set n' i p) with
                   | SomeE p' => SomeE (trm_car p')
                   | NoneE s => NoneE s
                   end
    | trm_cdr p => match (handle_assigning_set n' i p) with
                   | SomeE p' => SomeE (trm_cdr p')
                   | NoneE s => NoneE s
                   end
    | t => SomeE t
    end
  end

with handle_assigning_set_list (n i : nat) (ts : list trm) :=
  match n with
  | O => NoneE "Too many recursive calls"
  | S n' =>
    match ts with
    | nil => SomeE nil
    | t :: ts' => let e_t := (handle_assigning_set n' i t) in
                  let e_ts := (handle_assigning_set_list n' i ts) in
                  match e_t, e_ts with
                  | SomeE t', SomeE ts' => SomeE (t' :: ts')
                  | NoneE s, _ => NoneE s
                  | _, NoneE s => NoneE s
                  end
    end
  end.