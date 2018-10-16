Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.

(* Pattern match in Ltac *)

Ltac find_if :=
  match goal with
    | [ |- if ?X then _ else _ ] => destruct X
  end.

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
  intros; repeat find_if; constructor.
Qed.

(* One can use context for more powerful patterns. Can also reuse the
   bound context later.  *)

Ltac find_if_inside :=
  match goal with
    | [ |- context f[if ?X then _ else _] ] => destruct X
  end.

Theorem hmm' : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
  intros; repeat find_if_inside; constructor.
Qed.

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
  intros; repeat find_if_inside; reflexivity.
Qed.

(* A common idiom: repeat match. Notice the non-linear patterns *)

Ltac my_tauto :=
  repeat match goal with
           | [ H : ?P |- ?P ] => exact H

           | [ |- True ] => constructor
           | [ |- _ /\ _ ] => constructor
           | [ |- _ -> _ ] => intro

           | [ H : False |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ \/ _ |- _ ] => destruct H

           | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
         end.

Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
    my_tauto.
  Qed.
End propositional.

(* Caveat: pattern-matching is syntactic *)
Definition TTrue := True.

Goal TTrue.
  unfold TTrue;
  match goal with
    | [ |- True ] => constructor
  end.
Abort.

(* Another important difference: backtracking semantics *)

Theorem m1 : True.
  match goal with
    | [ |- _ ] => intro
    | [ |- True ] => constructor
  end.
Qed.

Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
  intros; match goal with
            | [ H : _ |- _ ] => idtac H
          end.

  (* Prints H : P *)

  match goal with
    | [ H : _ |- _ ] => exact H
  end.

  (* Tries in the same order, but succeeds only with H1 : Q *)
Qed.

(* Can also fail more and avoid backtracking: [fail n] fails but also
   breaks out of n enclosing match expressions (also works with ||)*)

Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

(* type of a term *)

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

(* Of course, can use unification to do this too *)

Ltac my_type_of t :=
  let P := constr:(t = t) in
  match P with
    | @eq ?T _ _ => T
  end.

Goal False.
  let TT := my_type_of 1 in
  set (T := TT).
Abort.

(* Application: simple solver for first-order formulas *)

Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro (* Works for implications too *)
           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
             (* avoids repeating more patterns *)
         end.


Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall x, P x -> S x.
    completer.
    (** [[
  x : A
  H : P x
  H0 : Q x
  H3 : R x
  H4 : S x
  ============================
   S x
   ]]
   *)

    assumption.
  Qed.

End firstorder.

(* Be careful, though... *)

Ltac completer' :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H') (* Here *)
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.


Section firstorder'.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo' : forall x, P x -> S x.
    (* completer' *)
  Abort.
End firstorder'.

(* Problem: elements bound by patterns cannot refer to bound variables *)

Theorem t1 : forall x : nat, x = x.
  match goal with
    | [ |- forall x, _ ] => trivial
  end.
Qed.

Theorem t1' : forall x : nat, x = x.
(** %\vspace{-.25in}%[[
  match goal with
    | [ |- forall x, ?P ] => trivial
  end.
]]

<<
User error: No matching clauses for match goal
>>
*)

Abort.

(* What if we want to bind predicates ? *)

Goal forall x : nat, x = x -> x + 4 = 4.
(*
  match goal with
    | |- forall x, ?P x -> _ => pose P
  end.
*)

(* Use @? patterns *)

  match goal with
    | |- forall x, @?P x -> _ => pose P
  end.
Abort.

Module Exercise0.

  (* Exercise: Simple Ltac programming *)

  (* Write a tactic [catch n t] that runs t and catches up to
     n levels of failure, failing with n + 1.

     Hint: lazymatch is a variant of match that does not perform
     backtracking and doesn't catch errors. Try using that if you get
     stuck. *)


  Goal False.
    catch 2 ltac:(fail 2).
    catch 3 ltac:(fail 3).
    catch 100 ltac:(fail 101) || idtac "that one failed".
  Abort.

  (* Write a tactic [hasVar t] that succeeds iff term [t] has a
     variable *)

  Goal forall n m p, n + m + p = 0.
    intros.
    hasVar (n + m).
    hasVar (p * p + 4).
    hasVar 7 || idtac "that one failed".
  Abort.

  (* Write a tactic [notTac t] that succeeds iff tactic [t] fails (at
     level 0). *)

  Goal False.
    notTac fail.
    notTac ltac:(apply H).
    notTac idtac || idtac "that one failed".
  Abort.

End Exercise0.

(** * Functional Programming in Ltac *)


(* Let's try to write length... *)

(* First try *)

(*

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ls' => S (length ls')
  end.
<<
Error: The reference ls' was not found in the current environment
>>

*)

(* Patterns need an explicit ? *)

(*

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => S (length ls')
  end.

<<
Error: The reference S was not found in the current environment
>>

*)

(* Escape terms using constr: *)

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' => constr:(S (length ls'))
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
Abort.

Reset length.

(* Problem: recursive length call is actually a call to the normal Coq length

   Solution: Use a let *)

Ltac length ls :=
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.

  (* But... *)

  (*
  generalize (@nil nat).
  intros l.
  let n := length (1 :: 2 :: l) in
    pose n.
  *)
Abort.

Ltac map T f :=
  let rec map' ls :=
    match ls with
      | nil => constr:(@nil T) (* Notice the explicit T *)
      | ?x :: ?ls' =>
        let x' := f x in
          let ls'' := map' ls' in
            constr:(x' :: ls'')
    end in
  map'.

Goal False.
  (* Needs escaping when passing tactics *)
  let ls := map (nat * nat)%type ltac:(fun x => constr:(x, x)) (1 :: 2 :: 3 :: nil) in
    pose ls.
Abort.

Module Exercise1.

(* Exercise: write foldl in Ltac. Make sure that the following test
   proof script works with it. *)

Theorem t : True.
  let n := foldl ltac:(fun a b => constr:(a + b)) 0 (1 :: 2 :: 3 :: nil) in
  let n' := eval compute in n in
    pose n'.
  assert (n = 6).
  reflexivity.
  trivial.
Qed.

Module Exercise1.

Reset length.

Ltac length ls :=
  idtac ls;
  match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.

(** Coq accepts the tactic definition, but the code is fatally flawed and will always lead to dynamic type errors. *)

Goal False.
(*
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
<<
Error: variable n should be bound to a term.
>> *)
Abort.

Reset length.

(* An Ltac term evaluates either to a Coq term, an integer or a
   tactic. The sequencing operator expects two tactics, however.

   Solution: Continuation-passing style! (??????)

*)

Ltac length ls k :=
  idtac ls;
  match ls with
    | nil => k O
    | _ :: ?ls' => length ls' ltac:(fun n => k (S n))
  end.

Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
(** [[
(1 :: 2 :: 3 :: nil)
(2 :: 3 :: nil)
(3 :: nil)
nil
]]
*)
Abort.

(* Recursive proof search *)

Ltac inster n :=
  intuition;
    match n with
      | S ?n' =>
        match goal with
          | [ H : forall x : ?T, _, y : ?T |- _ ] => generalize (H y); inster n'
        end
    end.

Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
    eauto.
  Restart.
    inster 2.
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
    eauto. (* doesn't work! *)
    inster 3.
  Qed.
End test_inster.

(* Recursive term manipulation *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.

Theorem and_True_prem : forall P Q,
  (P /\ True --> Q)
  -> (P --> Q).
  imp.
Qed.

Theorem and_True_conc : forall P Q,
  (P --> Q /\ True)
  -> (P --> Q).
  imp.
Qed.

Theorem assoc_prem1 : forall P Q R S,
  (P /\ (Q /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem assoc_prem2 : forall P Q R S,
  (Q /\ (P /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
  imp.
Qed.

Theorem comm_prem : forall P Q R,
  (P /\ Q --> R)
  -> (Q /\ P --> R).
  imp.
Qed.

Theorem assoc_conc1 : forall P Q R S,
  (S --> P /\ (Q /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem assoc_conc2 : forall P Q R S,
  (S --> Q /\ (P /\ R))
  -> (S --> (P /\ Q) /\ R).
  imp.
Qed.

Theorem comm_conc : forall P Q R,
  (R --> P /\ Q)
  -> (R --> Q /\ P).
  imp.
Qed.

Ltac search_prem tac :=
  let rec search P :=
    tac
    || (apply and_True_prem; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply assoc_prem1; search P1)
           || (apply assoc_prem2; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ --> _ ] => search P
       | [ |- _ /\ ?P --> _ ] => apply comm_prem; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_prem; tac))
     end.

Ltac search_conc tac :=
  let rec search P :=
    tac
    || (apply and_True_conc; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply assoc_conc1; search P1)
           || (apply assoc_conc2; search P2)
       end
  in match goal with
       | [ |- _ --> ?P /\ _ ] => search P
       | [ |- _ --> _ /\ ?P ] => apply comm_conc; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_conc; tac))
     end.

Theorem False_prem : forall P Q,
  False /\ P --> Q.
  imp.
Qed.

Theorem True_conc : forall P Q : Prop,
  (P --> Q)
  -> (P --> True /\ Q).
  imp.
Qed.

Theorem Match : forall P Q R : Prop,
  (Q --> R)
  -> (P /\ Q --> P /\ R).
  imp.
Qed.

Theorem ex_prem : forall (T : Type) (P : T -> Prop) (Q R : Prop),
  (forall x, P x /\ Q --> R)
  -> (ex P /\ Q --> R).
  imp.
Qed.

Theorem ex_conc : forall (T : Type) (P : T -> Prop) (Q R : Prop) x,
  (Q --> P x /\ R)
  -> (Q --> ex P /\ R).
  imp.
Qed.

(* Base case *)

Theorem imp_True : forall P,
  P --> True.
  imp.
Qed.

Ltac matcher :=
  intros;
    repeat search_prem ltac:(simple apply False_prem || (simple apply ex_prem; intro));
      repeat search_conc ltac:(simple apply True_conc || simple eapply ex_conc
        || search_prem ltac:(simple apply Match));
      try simple apply imp_True.

Theorem t2 : forall P Q : Prop,
  Q /\ (P /\ False) /\ P --> P /\ Q.
  matcher.
Qed.

Print t2.

Theorem t3 : forall P Q R : Prop,
  P /\ Q --> Q /\ R /\ P.
  matcher.
Abort.

(* One case that requires instantiation. *)

Theorem t4 : forall (P : nat -> Prop) Q, (exists x, P x /\ Q) --> Q /\ (exists x, P x).
  matcher.
Qed.

Print t4.

Module Exercise2.

(* Exercise: expression simplifier

   Write an expression simplifier to solve equalities between
   expressions of natural numbers, involving constants, plus and
   times, without using ring or similar tactics. To keep things
   simple, you don't have to solve goals that require commutativity of
   plus and times, or distributivity. Just deal with proofs that
   involve associativity and 0/1 removal. You should be able to use
   your tactic to prove the goals below.

*)

Theorem t1 : forall n m, n * (m * (m + 0)) = n * m * m.
  simplifier.
Qed.

Theorem t2 : forall n, n * (n + (n * 0 + 0)) + n * n * n * (0 + 0) = n * n.
  simplifier.
Qed.

Theorem t3 : forall n m p, 3 * n + p * m = n + n + n + p * m.
  simplifier.
Qed.

Theorem t4 : forall n m, 2 * n * (0 + m * 0 + (m + m * (1 + n * 0))) =
  (n + n) * (2 * m).
  simplifier.
Qed.

End Exercise2.

Module Exercise3.

  (* Exercise (adapted from CPDT): We are going to write a [falsify]
     tactic to prove goals of the form [~ forall n1 n2 ... : nat, P n1
     n2 ...], where [P] involves only equality and functions on
     [nat]. The tactic should take one argument [n], which bounds the
     greatest [nat] that can be tried for each one of the variables *)

  Theorem t1 : ~ forall n m p, n + n = p * m * m + 4.
    falsify 0.
  Qed.

  Theorem t2 : ~ forall a b c, a * a + b * b = c * c.
    falsify 1.
  Qed.

  Theorem t3 : ~ forall n m, n - m + m = n.
    falsify 1.
  Qed.

  Theorem t4 : ~ forall n, n * (n - 1) * (n - 2) * (n - 3) * (n - 4) =
                           n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n + 1).
    falsify 5.
  Qed.

End Exercise3.


(** * Creating Unification Variables *)

Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
  intros.

  (* Instead of applying H, let's see if Coq can find which variable to use
     here *)

  evar (y : nat).
  let y' := eval unfold y in y in
    clear y; specialize (H y').
  (* Apply tries to unify the evar here *)
  apply H.
Qed.

Ltac insterU H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             let x := fresh "x" in
               evar (x : T);
               let x' := eval unfold x in x in
                 clear x; specialize (H x')
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
  intro H; insterU H; apply H.
Qed.

(* We need to be careful when binding new variables in the context, as
   they might be already bound *)

Ltac my_intros :=
  repeat match goal with
           | |- forall v, _ => intros x
         end.

Goal forall x y, x + y = 0.
  my_intros.
Abort.

(* Solution: use the fresh tactic *)

Reset my_intros.
Ltac my_intros :=
  repeat match goal with
           | |- forall v, _ =>
             let x := fresh "x" in
             intros x
         end.

Goal forall x y, x + y = 0.
  my_intros.
Abort.

Ltac insterKeep H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros.
    eauto.
    firstorder.
    do 2 insterKeep H1.
    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end.

    (** Now the goal is simple enough to solve by logic programming. *)

    eauto.
  Qed.
End t6.

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros; do 2 insterKeep H1;
      repeat match goal with
               | [ H : ex _ |- _ ] => destruct H
             end; eauto.
  Abort.
End t7.

Reset insterU.

Ltac insterU tac H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T) by solve [ tac ];
                     specialize (H H'); clear H')
                 || fail 1
               | _ =>
                 let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

Ltac insterKeep tac H :=
  let H' := fresh "H'" in
    generalize H; intro H'; insterU tac H'.

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
    intros; do 2 insterKeep ltac:(idtac; match goal with
                                           | [ H : Q ?v |- _ ] =>
                                             match goal with
                                               | [ _ : context[P v _] |- _ ] => fail 1
                                               | _ => apply H
                                             end
                                         end) H1;
    repeat match goal with
             | [ H : ex _ |- _ ] => destruct H
           end; eauto.
  Qed.
End t7.

Theorem t8 : exists p : nat * nat, fst p = 3.
  econstructor; instantiate (1 := (3, 2)); reflexivity.
Qed.

Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.

Theorem t9 : exists p : nat * nat, fst p = 3.
  econstructor; match goal with
                  | [ |- fst ?x = 3 ] => equate x (3, 2)
                end; reflexivity.
Qed.

Module Exercise4.

  (* Exercise: Datastructures for tactics

     Datastructures can be very helpful when building more powerful
     and expressive tactics. For instance, tactics like [auto] or
     [autorewrite] use hint databases. Since Ltac can manipulate
     regular Coq terms, we can emulate some of that functionality in
     the tactics language using the tools we've seen in this
     chapter. *)

  (* Part 1 (taken from CPDT)

     When rewriting with a database, [autorewrite] doesn't
     backtrack. If it is able to perform a rewrite using some lemma
     and fails later, it won't try to rewrite with a different one
     before stopping.

     Write a [rewriter] tactic that adds backtracking to the basic
     functionality of [autorewrite]. Specifically, [rewriter] takes
     two arguments: 1- a list of lemmas to rewrite with, encoded as
     nested tuples terminated by [tt]; and 2- a number that bounds the
     rewrite sequences that are tried. Have a look at the [test]
     theorem below for an example. By the way, this is why we pass
     [tt] to [crush']: the first argument is a tuple list of
     additional lemmas for it to use. *)


  Section TestRewriter.

    (* Basic group theory *)

    Variable G : Type.
    Variable e : G.
    Variable i : G -> G.
    Variable mul : G -> G -> G.

    Local Infix "*" := mul.

    Hypothesis mul_assoc : forall a b c, a * b * c = a * (b * c).
    Hypothesis left_identity : forall a, e * a = a.
    Hypothesis right_identity : forall a, a * e = a.
    Hypothesis right_inverse : forall a, a * i a = e.
    Hypothesis left_inverse : forall a, i a * a = e.


    Theorem test1 : forall a, a * e * i a * i e = e.
      intros.
      (* This should solve the goal *)
      (* rewriter (right_identity, (right_inverse, tt)) 5. *)
    Abort.

    Theorem test2: (forall a, a * a * a = e) ->
      forall a, e * a * a * a * a * e = a.
      intros H a.
      (* This should solve the goal *)
      (* rewriter (H, (left_identity, (right_identity, tt))) 4. *)
    Abort.
  End TestRewriter.

  (* Part 2

     Unfortunately, it is not possible to use regular Coq datatypes to
     store tactics. However, with some creativity, one can find ways
     of circumventing this restriction.

     Implement lists at the tactic level. Your implementation should
     include two list-building tactics [tnil] and [tcons], plus a way
     of using the lists. Use your implementation to write two tactics
     [first_to_work] and [first_to_progress] that take a list of
     tactics as its argument. The first one should execute all the
     tactics in its list until it finds one that doesn't fail, failing
     if no tactics work (i.e., it is our version of the [first]
     operator). The second one should run all of its tactics until it
     finds one that does progress, failing otherwise (i.e. analogous
     to the || operator). Test your implementations on the example
     below. *)


  Ltac my_tactics_db := tcons idtac ltac:(tcons trivial tnil).

  Goal True.
    (* first_to_work my_tactics_db. *) (* Doesn't solve the goal *)
    (* first_to_progress my_tactics_db. *) (* Solves the goal *)
  Abort.

  (* Part 3: Application: tactic instrumentation

     Use your tactic list implementation to write a
     [find_first_to_solve] tactic. It should take a list of tactics as
     its argument and find the first one to solve the current
     goal. However, instead of closing the goal when it finds a
     solution, it should keep the goal and record the index of which
     tactic succeeded in a variable named [result].

     One could generalize this idea and try e.g. to write a variant of
     [auto] that takes a tactic database as an argument and returns an
     histogram of how many subgoals each tactic solved

     Hint: Use existential variables *)

  Goal True.
    (* find_first_to_solve my_tactics_db. *)
    (* Context now should have "result := 1 : nat" *)
  Abort.

End Exercise4.
