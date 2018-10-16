Require Import Arith String Dependent.

Set Implicit Arguments.

Inductive type :=
| Nat
| Bool
| Pair : type -> type -> type.


Inductive expr : type -> Set :=
| Var : string -> forall t, expr t
| Const : nat -> expr Nat
| Plus : expr Nat -> expr Nat -> expr Nat
| Times : expr Nat -> expr Nat -> expr Nat
| Tru : expr Bool
| Fals : expr Bool
| Eq : expr Nat -> expr Nat -> expr Bool
| IfThenElse : expr Bool -> forall t, expr t -> expr t -> expr t

| MkPair : forall t u, expr t -> expr u -> expr (Pair t u)
| Fst : forall t u, expr (Pair t u) -> expr t
| Snd : forall t u, expr (Pair t u) -> expr u.

Fixpoint typeD (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Pair t1 t2 => typeD t1 * typeD t2
  end%type.

Section vars.
  Variable vars : string -> forall t, typeD t.

  Fixpoint eval (t : type) (e : expr t) : typeD t :=
    match e with
      | Var x t => vars x t
      | Const n => n
      | Plus e1 e2 => eval e1 + eval e2
      | Times e1 e2 => eval e1 * eval e2
      | Tru => true
      | Fals => false
      | Eq e1 e2 => beq_nat (eval e1) (eval e2)
      | IfThenElse e _ e1 e2 => if eval e then eval e1 else eval e2

      | MkPair _ _ e1 e2 => (eval e1, eval e2)
      | Fst _ _ e1 => fst (eval e1)
      | Snd _ _ e1 => snd (eval e1)
    end.

  Hint Extern 1 (_ = _) => congruence.

  Definition pairOut t (e : expr t) : option (match t with
                                                | Pair t1 t2 => expr t1 * expr t2
                                                | _ => unit
                                              end) :=
    match e with
      | MkPair _ _ e1 e2 => Some (e1, e2)
      | _ => None
    end.

  Fixpoint cfold t (e : expr t) : expr t :=
    match e with
      | Var x t => Var x t
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
      | Tru => Tru
      | Fals => Fals
      | Eq e1 e2 =>
        match cfold e1, cfold e2 with
          | Const n1, Const n2 => if beq_nat n1 n2 then Tru else Fals
          | e1', e2' => Eq e1' e2'
        end
      | IfThenElse e _ e1 e2 =>
        match cfold e with
          | Tru => cfold e1
          | Fals => cfold e2
          | e' => IfThenElse e' (cfold e1) (cfold e2)
        end

      | MkPair _ _ e1 e2 => MkPair (cfold e1) (cfold e2)
      | Fst _ _ e1 =>
        let e1' := cfold e1 in
          match pairOut e1' with
            | Some p => fst p
            | _ => Fst e1'
          end
      | Snd _ _ e1 =>
        let e1' := cfold e1 in
          match pairOut e1' with
            | Some p => snd p
            | _ => Snd e1'
          end
    end.
  
  Require Import Dependent.

  Theorem cfold_sound : forall t (e : expr t), eval (cfold e) = eval e.
    induction e; simpl; unfold pairOut; intuition;
      repeat (match goal with
                | [ |- context[match cfold ?E with Const _ => _ | _ => _ end] ] =>
                  dep_destruct (cfold E)
                | [ |- context[fst ?E] ] => destruct E
                | [ |- context[snd ?E] ] => destruct E
                | [ H : _ = _ |- _ ] => rewrite H in *
                | [ |- context[if ?E then _ else _] ] => destruct E
              end; simpl in *; intuition).
  Qed.
End vars.
