Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Eqdep.

(**
  Objects that can be passed around in Ltac include:
  - tactics
  - tuples
  - Gallina terms
  - Gallina types
  
  Lists of hypotheses are represented as right-associated nested tuples, with the hypothesis tt representing the empty list.
*)

(* Usable in Ltac unit tests. It's usually necessary to inline this, as Ltac doesn't support call by name. *)
Ltac fails tac := (tac; fail 1) || idtac.

Goal True.
  fails fail.
  Fail fails idtac.
Abort.

Ltac subst' := try subst.

Goal forall (x y: nat), x = y -> x = y.
  intros.
  progress subst'.
  (* infaillible *)
  fails ltac:(progress subst').
  (* no-op *)
  subst'.
  exact eq_refl.
Qed.

Ltac inList x ls :=
  match ls with
    | tt => fail "not in list"
    | (x, _) => idtac
    | (_, ?LS) => inList x LS
    | (_, _) => fail "not in list"
  end.

Goal True.
  inList True (True, tt).
  (inList True (False, tt); fail 1) || idtac.
Abort.

(* For f: hyp -> tactic, ls: list hyp; find a hypothesis in ls on which f succeeds*)
Ltac forSome f ls :=
  match ls with
    | tt => fail "not found"
    | (?X, ?LS) => f X || forSome f LS || fail 1 "not found"
  end.

Goal True.
  (forSome ltac:(fun x => exact x) (0, tt); fail 1) || idtac.
  forSome ltac:(fun x => exact x) (0, (I, tt)).
Qed.

(* For f: hyp -> tactic; find a hypothesis in context on which f succeeds *)
Ltac forSomeInCtx f :=
  match goal with
    | [ H : _ |- _ ] => f H || fail 1 "not found"
  end.

Goal True.
  pose 0 as A.
  (forSomeInCtx ltac:(fun x => exact x); fail 1) || idtac.
  pose I as B.
  forSomeInCtx ltac:(fun x => exact x).
Qed.

(* For f: hyp -> tactic, ls: list hyp; apply f to all hypotheses in ls, fail if any application doesn't succeed*)
Ltac forEach f ls :=
  match ls with
    | tt => idtac
    | (?X, ?LS) => f X; forEach f LS
    | (_, _) => fail 1
  end.

Goal True.
  (forEach ltac:(fun x => exact x) (0, (I, tt)); fail 1) || idtac.
  forEach ltac:(fun x => idtac) (I, (0, tt)).
Abort.

(* for H : hyp; perform inversion, revert if it doesn't solve the current goal *)
(* TODO needs test *)
Ltac invert0 H := inversion H; fail.

(* for H : hyp; perform inversion, revert if it doesn't generate exactly one goal *)
Ltac invert1 H := inversion H; [idtac]; clear H; subst'.

Goal True.
  pose true as A. Fail invSingle A.
  pose (I, I) as B. invert1 B.
  exact I.
Qed.

Ltac destructExistentialInCtx :=
  match goal with
    | [ H : ex _ |- _ ] => destruct H
  end.

Goal True.
  pose proof (ex_intro (eq I) I eq_refl).
  destructExistentialInCtx.
  assumption. (* TODO use the prop instead *)
Qed.

Ltac inCtx P := assert P; [ assumption | idtac ].

Goal True.
  Fail inCtx True.
  pose proof I.
  inCtx True.
Abort.

Ltac not tac :=
  (tac; fail 1) || idtac.
  
Goal True.
  Fail not idtac.
  not idtac || idtac "success". (* else branch *)
  not fail.
Abort.

Ltac notInCtx P := not ltac:(inCtx P).

Goal True.
  notInCtx True.
  pose proof I.
  Fail notInCtx True.
Abort.

Ltac injectionInCtx :=
  match goal with
  (* TODO is matching on G necessary? *)
  | [ H : ?F ?X = ?F ?Y |- ?G ] =>
    (* fail early if it wouldn't progress *)
    notInCtx (X = Y); 
    injection H;
    match goal with
      | [ |- X = Y -> G ] =>
        try clear H; 
        intros; 
        subst'
    end
  | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
    (* fail early if it wouldn't progress *)
    (notInCtx (X = Y) || notInCtx (U = V)); 
    injection H;
    match goal with
      | [ |- U = V -> X = Y -> G ] =>
        try clear H; 
        intros; 
        subst'
    end
  end.

Goal forall (x y : nat), S x = S y -> x = y.
  intros x y H.
  injectionInCtx.
  exact eq_refl.
Qed.

Goal forall (x y u v : nat), (x, u) = (y, v) -> x = y.
  intros x y u v H.
  injectionInCtx.
  exact eq_refl.
Qed.

Ltac invertInCtx :=
  let invert H := invert0 H || invert1 H in
  match goal with
  | [ H : ?F _ |- _ ] => invert H
  | [ H : ?F _ _ |- _ ] => invert H
  | [ H : ?F _ _ _ |- _ ] => invert H
  | [ H : ?F _ _ _ _ |- _ ] => invert H
  | [ H : ?F _ _ _ _ _ |- _ ] => invert H
  end.

Goal forall (A B : Prop), and A B -> A.
  intros.
  invertInCtx.
  assumption.
Qed.

Ltac invertInCtxExt ctors :=
  let invert H F := inList F ctors; invert0 H || invert1 H in
  match goal with
  | [ H : ?F _ |- _ ] => invert H F
  | [ H : ?F _ _ |- _ ] => invert H F
  | [ H : ?F _ _ _ |- _ ] => invert H F
  | [ H : ?F _ _ _ _ |- _ ] => invert H F
  | [ H : ?F _ _ _ _ _ |- _ ] => invert H F
  end.

Goal forall (A B : Prop), and A B -> A.
  intros.
  Fail invertInCtxExt (or, tt).
  invertInCtxExt (or, (and, tt)).
  assumption.
Qed.

(* lossy *)
Ltac injectSigmaInCtx :=
  match goal with
  | [ H : existT _ _ _ = existT _ _ _ |- _ ] => injection H; intro; clear H
  end.
  
Goal forall (x y : nat), (existT (fun x => True) x I) = (existT (fun x => True) y I) -> x = y.
  intros.
  injectSigmaInCtx.
  assumption.
Qed.

Ltac injectSigma2InCtx :=
  match goal with
  | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => pose proof (inj_pair2 _ _ _ _ _ H); clear H
  end.

Goal forall (x: nat) (A B : Nat.Even x), (existT Nat.Even x A) = (existT Nat.Even x B) -> A = B.
  intros.
  injectSigma2InCtx.
  assumption.
Qed.

Ltac rewrite' H := rewrite H by solve [auto].

Goal True.
Admitted.

Ltac rewriteInCtx :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

Goal True.
Admitted.

(** Used strictly for bookkeeping in inster. `done T tt` being in context means that  *)
Definition done {T : Type} (x : T) := True.

(** Maximally instantiate forall hypotheses *)
Ltac inster' e trace :=
  match type of e with
    | forall x : _, _ =>
      match goal with
        | [ H : _ |- _ ] =>
          inster' (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      match trace with
        | (_, _) =>
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              fail 1
            | _ =>
              let T := type of e in
                match type of T with
                  | Prop =>
                    pose proof e;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    forEach ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

Ltac clear_done := repeat match goal with [ H : done _ |- _ ] => clear H end.

Ltac inster e := inster' e tt; clear_done.

Goal (forall x: nat, Nat.Odd x) -> Nat.Odd 0.
  intros H.
  pose 0.
  inster H.
  assumption.
Qed.

