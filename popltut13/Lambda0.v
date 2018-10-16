Require Import Arith String.

Set Implicit Arguments.

Inductive type :=
| Nat
| Func : type -> type -> type.

Fixpoint typeD (t : type) : Set :=
  match t with
    | Nat => nat
    | Func dom ran => typeD dom -> typeD ran
  end.

Section var.
  Variable var : type -> Set.

  Inductive expr : type -> Set :=
  | Var : forall t, var t -> expr t
  | App : forall dom ran, expr (Func dom ran) -> expr dom -> expr ran
  | Abs : forall dom ran, (var dom -> expr ran) -> expr (Func dom ran)

  | Const : nat -> expr Nat
  | Plus : expr Nat -> expr Nat -> expr Nat
  | Times : expr Nat -> expr Nat -> expr Nat.
End var.

Implicit Arguments Var [var t].
Implicit Arguments Abs [var dom ran].
Implicit Arguments Const [var].

Definition Expr (t : type) := forall var, expr var t.

Example ident : Expr (Func Nat Nat) := fun _ => Abs (fun x => Var x).
Example app_ident : Expr Nat := fun _ => App (ident _) (Const 0).
Example dumb_ident : Expr (Func Nat Nat) := fun _ => Abs (fun x => Plus (Plus (Const 0) (Const 0)) (Var x)).

Fixpoint eval (t : type) (e : expr typeD t) : typeD t :=
  match e with
    | Var _ x => x
    | App _ _ e1 e2 => (eval e1) (eval e2)
    | Abs _ _ e1 => fun x => eval (e1 x)

    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Times e1 e2 => eval e1 * eval e2
  end.

Definition Eval t (E : Expr t) : typeD t :=
  eval (E typeD).

Eval compute in Eval ident.
Eval compute in Eval app_ident.
Eval compute in Eval dumb_ident.

Fixpoint cfold var t (e : expr var t) : expr var t :=
  match e with
    | Var _ x => Var x
    | App _ _ e1 e2 => App (cfold e1) (cfold e2)
    | Abs _ _ e1 => Abs (fun x => cfold (e1 x))

    | Const n => Const n
    | Plus e1 e2 =>
      match cfold e1, cfold e2 with
        | Const n1, Const n2 => Const (n1 + n2)
        | e1', e2' => Plus e1' e2'
      end
    | Times e1 e2 =>
      match cfold e1, cfold e2 with
        | Const n1, Const n2 => Const (n1 * n2)
        | e1', e2' => Times e1' e2'
      end
  end.

Definition Cfold t (E : Expr t) : Expr t := fun var => cfold (E var).

Eval compute in Cfold ident.
Eval compute in Cfold app_ident.
Eval compute in Cfold dumb_ident.

Hint Extern 1 (_ = _) => congruence.

Require Import Dependent FunctionalExtensionality.

Lemma cfold_sound : forall t (e : expr typeD t), eval (cfold e) = eval e.
  induction e; simpl; intuition;
    repeat (match goal with
              | [ |- context[match cfold ?E with Const _ => _ | _ => _ end] ] =>
                dep_destruct (cfold E)
              | _ => apply functional_extensionality; intro
            end; simpl in *; subst; intuition).
Qed.

Theorem Cfold_sound : forall t (E : Expr t), Eval (Cfold E) = Eval E.
  intros; apply cfold_sound.
Qed.
