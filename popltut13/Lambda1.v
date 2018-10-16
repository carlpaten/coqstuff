Require Import Arith String.

Set Implicit Arguments.

Inductive type :=
| Nat
| Func : type -> type -> type
| Pair : type -> type -> type.

Fixpoint typeD (t : type) : Set :=
  match t with
    | Nat => nat
    | Func dom ran => typeD dom -> typeD ran
    | Pair t1 t2 => typeD t1 * typeD t2
  end%type.

Section var.
  Variable var : type -> Set.

  Inductive expr : type -> Set :=
  | Var : forall t, var t -> expr t
  | App : forall dom ran, expr (Func dom ran) -> expr dom -> expr ran
  | Abs : forall dom ran, (var dom -> expr ran) -> expr (Func dom ran)

  | Const : nat -> expr Nat
  | Plus : expr Nat -> expr Nat -> expr Nat
  | Times : expr Nat -> expr Nat -> expr Nat

  | MkPair : forall t u, expr t -> expr u -> expr (Pair t u)
  | Fst : forall t u, expr (Pair t u) -> expr t
  | Snd : forall t u, expr (Pair t u) -> expr u.
End var.

Implicit Arguments Var [var t].
Implicit Arguments Abs [var dom ran].
Implicit Arguments Const [var].

Definition Expr (t : type) := forall var, expr var t.

Example ident : Expr (Func Nat Nat) := fun _ => Abs (fun x => Var x).
Example app_ident : Expr Nat := fun _ => App (ident _) (Const 0).
Example dumb_ident : Expr (Func Nat Nat) := fun _ => Abs (fun x => Plus (Plus (Const 0) (Const 0)) (Var x)).

Example one_two : Expr (Pair Nat Nat) := fun _ => MkPair (Const 1) (Const 2).
Example one : Expr Nat := fun _ => Fst (one_two _).

Fixpoint eval (t : type) (e : expr typeD t) : typeD t :=
  match e with
    | Var x => x
    | App e1 e2 => (eval e1) (eval e2)
    | Abs e1 => fun x => eval (e1 x)

    | Const n => n
    | Plus e1 e2 => eval e1 + eval e2
    | Times e1 e2 => eval e1 * eval e2

    | MkPair e1 e2 => (eval e1, eval e2)
    | Fst e1 => fst (eval e1)
    | Snd e1 => snd (eval e1)
  end.

Definition Eval t (E : Expr t) : typeD t :=
  eval (E typeD).

Eval compute in Eval ident.
Eval compute in Eval app_ident.
Eval compute in Eval dumb_ident.

Eval compute in Eval one_two.
Eval compute in Eval one.

Definition pairOut var t (e : expr var t) : option (
  match t with
  | Pair t1 t2 => expr var t1 * expr var t2
  | _ => unit
  end
 ) :=
  match e with
  | MkPair e1 e2 => Some (e1, e2)
  | _ => None
  end.

Fixpoint cfold var t (e : expr var t) : expr var t :=
  match e with
    | Var x => Var x
    | App e1 e2 => App (cfold e1) (cfold e2)
    | Abs e1 => Abs (fun x => cfold (e1 x))

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

    | MkPair e1 e2 => MkPair (cfold e1) (cfold e2)
    | Fst e1 =>
      let e1' := cfold e1 in
        match pairOut e1' with
          | Some p => fst p
          | _ => Fst e1'
        end
    | Snd e1 =>
      let e1' := cfold e1 in
        match pairOut e1' with
          | Some p => snd p
          | _ => Snd e1'
        end
  end.

Definition Cfold t (E : Expr t) : Expr t := fun var => cfold (E var).

Eval compute in Cfold ident.
Eval compute in Cfold app_ident.
Eval compute in Cfold dumb_ident.

Eval compute in Cfold one_two.
Eval compute in Cfold one.

Hint Extern 1 (_ = _) => congruence.

Require Import Dependent FunctionalExtensionality.

Lemma cfold_sound : forall t (e : expr typeD t), eval (cfold e) = eval e.
  induction e; simpl; unfold pairOut; intuition;
    repeat (match goal with
              | [ |- context[match cfold ?E with Const _ => _ | _ => _ end] ] =>
                dep_destruct (cfold E)
              | _ => apply functional_extensionality; intro
              | [ |- context[fst ?E] ] => destruct E
              | [ |- context[snd ?E] ] => destruct E
            end; simpl in *; subst; intuition).
Qed.

Theorem Cfold_sound : forall t (E : Expr t), Eval (Cfold E) = Eval E.
  intros; apply cfold_sound.
Qed.
