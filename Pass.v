From vchez Require Export Definitions.

(* 
convert_assignments
has-assigning-set
handle-assigning-set


Fixpoint has_assigning_set (i : nat) (t : trm) : bool :=
  match t with
  | trm_let v ts => has_assigning_set_list (S i) ts
  | trm_abs ts => has_assigning_set_list (S i) ts
  | trm_app t1 t2 => orb (has_assigning_set i t1) (has_assigning_set i t2)
  | trm_set x t1 => match x with
                    | (trm_var (bvar n)) => if (i =? n) then true else has_assigning_set i t1
                    | _ => has_assigning_set i t1
                    end
  | trm_setcar p v => orb (has_assigning_set i p) (has_assigning_set i v)
  | trm_setcdr (pair : trm)(v : trm)
  | trm_cons (v1 : trm)(v2 : trm)
  | trm_car (pair : trm)
  | trm_cdr (pair : trm)
  | trm_var  (x : ln_var)
  | trm_pp (n : name)
  | trm_num (i : nat)
  | trm_null
  | trm_true
  | trm_false
*)