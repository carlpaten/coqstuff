Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.

Module Exercise0.

  (* Exercise: Simple Ltac programming *)

  (* Write a tactic [catch n t] that runs t and catches up to
     n levels of failure, failing with n + 1.

     Hint: lazymatch is a variant of match that does not perform
     backtracking and doesn't catch errors. Try using that if you get
     stuck. *)

  (* Solution *)
  Ltac catch n t :=
    match n with
      | O => t
      | S ?n' => catch n' t
      | _ => idtac
    end.
  (* End solution *)

  Goal False.
    catch 0 ltac:(fail).
    catch 2 ltac:(fail 2).
    catch 3 ltac:(fail 3).
    (* This line should fail *)
    (* catch 100 ltac:(fail 101). *)
  Abort.

  (* Write a tactic [hasVar t] that succeeds iff term [t] has a
     variable *)

  (* Solution *)
  Ltac hasVar t :=
    match goal with
      | v : _ |- _ =>
        match t with
          | context[v] => idtac
        end
    end.
  (* End solution *)

  Goal forall n m p, n + m + p = 0.
    intros.
    hasVar (n + m).
    hasVar (p * p + 4).
    (* This line should fail *)
    (* hasVar 7. *)
  Abort.

  (* Write a tactic [notTac t] that succeeds iff tactic [t] fails (at
     level 0). *)

  (* Solution *)
  Ltac notTac t :=
    first [t; fail 1 | idtac].
  (* End solution *)

  Goal False.
    notTac fail.
    notTac ltac:(apply H).
    (* This line should fail *)
    (* notTac idtac. *)
  Abort.

End Exercise0.

Module Exercise1.

(* Exercise: expression simplifier

   Write an expression simplifier to solve equalities between
   expressions of natural numbers, involving constants, plus and
   times, without using ring or similar tactics. To keep things
   simple, you don't have to solve goals that require commutativity of
   plus and times, or distributivity. Just deal with proofs that
   involve associativity and 0/1 removal. You should be able to use
   your tactic to prove the goals below.

*)

(* Solution *)

Ltac simplifier :=
  intros;
  repeat (
    simpl;
    match goal with
      | |- context[?n * 1] => rewrite (Mult.mult_1_r n)
      | |- context[?n * 0] => rewrite (Mult.mult_0_r n)
      | |- context[?n * (?m * ?p)] => rewrite (Mult.mult_assoc n m p)
      | |- context[?n + 0] => rewrite (Plus.plus_0_r n)
      | |- context[?n + (?m + ?p)] => rewrite (Plus.plus_assoc n m p)
    end
  );
  try reflexivity.

(* End Solution *)

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

End Exercise1.

Module Exercise2.

  (* Exercise: Datastructures for tactics *)

  (* Part 1

     It is not possible to use regular Coq datatypes to store
     tactics. However, with some creativity, one can find ways of
     circumventing this restriction.

     Implement lists at the tactic level. Your implementation should
     include two list-building tactics [tnil] and [tcons], plus a
     pattern-matching tactic [tmatch]. [tnil] and [tcons] should work
     like their Gallina counterparts: [tnil] takes no arguments and
     represents the empty list; [tcons] takes two arguments, a tactic
     [t] and a tactic list [ts], and returns [ts] with [t] put at the
     front. [tmatch] takes a tactic list [ts], a tactic with no
     arguments to be executed when [ts] is empty, and a two-argument
     tactic to be executed with the appropriate arguments when [ts] is
     non-empty. *)

  (* Solution *)
  Ltac tnil := fun cnil ccons => cnil.
  Ltac tcons t ts := fun cnil ccons => ccons t ts.
  Ltac tmatch ts cnil ccons := ts cnil ccons.
  (* End solution *)

  (* Part 2

     Use your tactic list implementation to write two tactics
     [first_to_work] and [first_to_progress] that take a list of
     tactics as its argument. The first one should execute all the
     tactics in its list until it finds one that doesn't fail, failing
     if no tactics work (i.e., it is our version of the [first]
     operator). The second one should run all of its tactics until it
     finds one that does progress, failing otherwise (i.e. analogous
     to the || operator). Test your implementations on the example
     below. *)

  (* Solution *)
  Ltac first_to_work ts :=
    tmatch ts
      fail
      ltac:(fun t rest => first [t | first_to_work rest]).

  Ltac first_to_progress ts :=
    tmatch ts
      fail
      ltac:(fun t rest => t || first_to_progress rest).
  (* End solution *)

  Ltac my_tactics_db := tcons idtac ltac:(tcons trivial tnil).

  Goal True.
    (* first_to_work my_tactics_db. *) (* Doesn't solve the goal *)
    (* first_to_progress my_tactics_db. *) (* Solves the goal *)
  Abort.

  (* Part 3: Application: tactic instrumentation

     Write a [find_first_to_solve] tactic, that takes a list of
     tactics as its argument and finds the first one to solve the
     current goal. However, instead of closing the goal when it finds
     a solution, it should keep the goal and record the index of which
     tactic succeeded in a variable named [result].

     One could generalize this idea and try e.g. to write a variant of
     [auto] that takes a tactic database as an argument and returns an
     histogram of how many subgoals each tactic solved

     Hint: Use existential variables *)

  (* Solution *)
  Ltac equate x y :=
    let dummy := constr:(eq_refl x : x = y) in idtac.

  Ltac find_first_to_solve ts :=
    let result := fresh "result" in
    evar (result : nat);
    let rec aux n ts :=
      ts fail ltac:(fun t rest =>
        solve [equate result n; t] || aux (S n) rest
      ) in
    match goal with
      | |- ?G =>
        let H := fresh "H" in
        assert (H : G); [aux 0 ts|clear H]
    end.
  (* End solution *)

  Goal True.
    (* find_first_to_solve my_tactics_db. *)
    (* Context now should have "result := 1 : nat" *)
  Abort.

End Exercise2.
