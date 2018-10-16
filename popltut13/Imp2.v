Require Import Arith String.
Open Scope string_scope.

Definition proc := string.
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
| Assert : invariant -> cmd
| Call : proc -> cmd.

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

Section procs.
  Variable procs : proc -> cmd.

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
    -> run en (Assert inv) en

  | RunCall : forall en p en',
    run en (procs p) en'
    -> run en (Call p) en'.

  Variables procPre procPost : proc -> invariant.
  
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

      | Call p =>
        (procPost p,
          (forall en, pre en -> procPre p en))
    end.

  Hypothesis goodSpecs : forall p,
    let (post, vc) := vcgen (procPre p) (procs p)
      in (forall en, procPre p en -> vc)
        /\ (forall en', post en' -> procPost p en').

  Theorem vcgen_sound : forall en c en', run en c en'
    -> forall (pre : invariant), pre en
      -> let (post, vc) := vcgen pre c in
        vc -> post en'.
    induction 1; simpl in *; intuition;
      repeat match goal with
               | [ p : proc |- _ ] => specialize (goodSpecs p)
               | [ IH : forall pre, pre _ -> let (post, vc) := vcgen pre ?C in _ |- context[vcgen ?PRE ?C] ] =>
                 specialize (IH PRE); destruct (vcgen PRE C)
               | [ IH : forall pre, pre _ -> let (post, vc) := vcgen pre ?C in _, _ : context[vcgen ?PRE ?C] |- _ ] =>
                 specialize (IH PRE); destruct (vcgen PRE C)
               | [ |- context[vcgen ?PRE ?C] ] =>
                 destruct (vcgen PRE C)
             end; intuition;
      try match goal with
            | [ _ : context[While ?inv _ _], IH : forall pre, pre _ -> _ |- _ ] =>
              destruct (IH inv); clear IH
          end; intuition eauto 6.
  Qed.
End procs.
