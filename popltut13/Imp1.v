Require Import Arith String.
Open Scope string_scope.

Definition var := string.

Inductive exp :=
| Var : var -> exp
| Const : nat -> exp
| Plus : exp -> exp -> exp.

Inductive relop := Eq | NotEq.

Record test := {
  Left : exp;
  Op : relop;
  Right : exp
}.

Definition env := var -> nat.
Definition invariant := env -> Prop.

Inductive cmd :=
| Assign : var -> exp -> cmd
| Seq : cmd -> cmd -> cmd
| If : test -> cmd -> cmd -> cmd
| While : invariant -> test -> cmd -> cmd
| Nondet : cmd -> cmd -> cmd
| Assert : invariant -> cmd.

Section env.
  Variable en : env.

  Fixpoint eval (e : exp) : nat :=
    match e with
      | Var x => en x
      | Const n => n
      | Plus e1 e2 => eval e1 + eval e2
    end.

  Definition rel (r : relop) : nat -> nat -> bool :=
    match r with
      | Eq => beq_nat
      | NotEq => fun n1 n2 => negb (beq_nat n1 n2)
    end.

  Definition check (t : test) : bool :=
    (rel (Op t)) (eval (Left t)) (eval (Right t)).
End env.

Definition upd (en : env) (x : var) (v : nat) : env :=
  fun x' => if string_dec x' x then v else en x'.

Inductive run : env -> cmd -> env -> Prop :=
| RunAssign : forall en x e,
  run en (Assign x e) (upd en x (eval en e))

| RunSeq : forall en c1 c2 en1 en2,
  run en c1 en1
  -> run en1 c2 en2
  -> run en (Seq c1 c2) en2

| RunIfTrue : forall en t c1 c2 en',
  check en t = true
  -> run en c1 en'
  -> run en (If t c1 c2) en'

| RunIfFalse : forall en t c1 c2 en',
  check en t = false
  -> run en c2 en'
  -> run en (If t c1 c2) en'

| RunIfWhileFalse : forall en inv t c,
  check en t = false
  -> run en (While inv t c) en

| RunIfWhileTrue : forall en inv t c en1 en2,
  check en t = true
  -> run en c en1
  -> run en1 (While inv t c) en2
  -> run en (While inv t c) en2

| RunNondetLeft : forall en c1 c2 en',
  run en c1 en'
  -> run en (Nondet c1 c2) en'

| RunNondetRight : forall en c1 c2 en',
  run en c2 en'
  -> run en (Nondet c1 c2) en'

| RunAssert : forall en (inv : invariant),
  inv en
  -> run en (Assert inv) en.

Fixpoint vcgen (pre : invariant) (c : cmd) : invariant * Prop :=
  match c with
    | Assign x e =>
      ((fun en => exists en', pre en' /\ en = upd en' x (eval en' e)),
        True)

    | Seq c1 c2 =>
      let (post1, vc1) := vcgen pre c1 in
      let (post2, vc2) := vcgen post1 c2 in
        (post2,
          vc1 /\ vc2)

    | If t c1 c2 =>
      let (post1, vc1) := vcgen (fun en => pre en /\ check en t = true) c1 in
      let (post2, vc2) := vcgen (fun en => pre en /\ check en t = false) c2 in
        ((fun en => post1 en \/ post2 en),
          vc1 /\ vc2)

    | While inv t c1 =>
      let (post1, vc1) := vcgen (fun en => inv en /\ check en t = true) c1 in
        ((fun en => inv en /\ check en t = false),
          (forall en, pre en -> inv en)
          /\ vc1
          /\ (forall en, post1 en -> inv en))

    | Nondet c1 c2 =>
      let (post1, vc1) := vcgen pre c1 in
      let (post2, vc2) := vcgen pre c2 in
        ((fun en => post1 en \/ post2 en),
          vc1 /\ vc2)

    | Assert inv =>
      (inv,
        (forall en, pre en -> inv en))
  end.

Fixpoint sumN (n : nat) :=
  match n with
    | O => O
    | S n' => sumN n' + n'
  end.

Example sum := Seq
  (Assign "i" (Const 0))
  (Seq
    (Assign "acc" (Const 0))
    (While (fun en => en "acc" = sumN (en "i"))
      {| Left := Var "i"; Op := NotEq; Right := Const 10 |}
      (Seq
        (Assign "acc" (Plus (Var "acc") (Var "i")))
        (Assign "i" (Plus (Const 1) (Var "i")))))).

Eval simpl in fun pre => vcgen pre sum.

Theorem vcgen_sound : forall en c en', run en c en'
  -> forall (pre : invariant), pre en
    -> let (post, vc) := vcgen pre c in
      vc -> post en'.
  induction 1; simpl in *; intuition eauto;
    repeat match goal with
             | [ IH : forall pre, pre _ -> let (post, vc) := vcgen pre ?C in _ |- context[vcgen ?PRE ?C] ] =>
               specialize (IH PRE); destruct (vcgen PRE C)
             | [ |- context[vcgen ?PRE ?C] ] =>
               destruct (vcgen PRE C)
           end; intuition;
    match goal with
      | [ _ : context[While ?inv _ _], IH : forall pre, pre _ -> _ |- _ ] =>
        destruct (IH inv); clear IH
    end; intuition.
Qed.

Lemma negb_beq_nat : forall n m, negb (beq_nat n m) = false
  -> n = m.
  intros; specialize (beq_nat_true n m); destruct (beq_nat n m); auto.
Qed.

Ltac verify := intros;
  match goal with
    | [ H : run _ _ _ |- _ ] => specialize (vcgen_sound _ _ _ H (fun _ => True));
      simpl; unfold check; simpl; destruct 1
  end;
  repeat match goal with
           | [ H : _ |- _ ] => apply negb_beq_nat in H
           | [ H : _ = _ |- _ ] => rewrite H in *
         end; firstorder subst; unfold upd; simpl; auto.

Lemma sum_correct : forall en en', run en sum en'
  -> en' "acc" = sumN 10.
  verify.
Qed.
