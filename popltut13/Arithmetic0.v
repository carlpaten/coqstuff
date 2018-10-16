Inductive expr :=
| Const : nat -> expr
| Plus : expr -> expr -> expr
| Times : expr -> expr -> expr.

Fixpoint eval (e : expr) : nat :=
  match e with
    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Times e1 e2 => eval e1 * eval e2
  end.
