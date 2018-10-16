Require Import String.

Inductive expr :=
| Var : string -> expr
| Const : nat -> expr
| Plus : expr -> expr -> expr
| Times : expr -> expr -> expr.

Fixpoint eval (vars : string -> nat) (e : expr) : nat :=
  match e with
    | Var x => vars x
    | Const n => n
    | Plus e1 e2 => eval vars e1 + eval vars e2
    | Times e1 e2 => eval vars e1 * eval vars e2
  end.

Fixpoint cfold (e : expr) : expr :=
  match e with
    | Var _ => e
    | Const _ => e
    | Plus e1 e2 => match cfold e1, cfold e2 with
                      | Const n1, Const n2 => Const (n1 + n2)
                      | e1', e2' => Plus e1' e2'
                    end
    | Times e1 e2 => match cfold e1, cfold e2 with
                       | Const n1, Const n2 => Const (n1 * n2)
                       | e1', e2' => Times e1' e2'
                     end
  end.

(* Here is an ugly manual proof. *)

Theorem cfold_sound : forall vars e, eval vars (cfold e) = eval vars e.
  induction e.

  simpl.
  reflexivity.

  simpl.
  reflexivity.

  simpl.
  destruct (cfold e1).
  simpl in *.
  rewrite IHe1.
  rewrite IHe2.
  reflexivity.
  destruct (cfold e2).
  simpl in *.
  (* Ran out of patience here! *)
Abort.

Hint Extern 1 (_ = _) => congruence.

Theorem cfold_sound : forall vars e, eval vars (cfold e) = eval vars e.
  induction e; simpl; intuition;
    repeat match goal with
             | [ |- context[match cfold ?E with Const _ => _ | _ => _ end] ] =>
               destruct (cfold E); simpl in *; intuition
           end.
Qed.
