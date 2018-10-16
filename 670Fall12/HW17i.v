Require Import CpdtTactics Arith List.
Set Implicit Arguments.

Section looping_autorewrite.

(* Exercise (5 mins): Write a set of lemmas and [Hint Rewrite]s to cause
   autorewrite to loop. Comment out the looping autorewrite so that the rest
   of the file can compile. *)

End looping_autorewrite.

Section STLC.

(* Exercise (2 hours): The following is a proof that the call-by-value
   simply-typed lambda calculus is type-safe. The proofs are all correct and
   work as written, with the proper hint databases. Supply the hints to build
   these databases. *)

Inductive type : Set :=
| UnitT : type
| Arrow : type -> type -> type.

Inductive expr : Set :=
| UnitE : expr
| Var : nat -> expr            (* Use deBruijn indices encoding *)
| Lam : type -> expr -> expr
| App : expr -> expr -> expr.

(* With deBruijn indices, the context is just an ordered list of types *)
Definition context := list type.

(* Like 'member', but explicitly tracks which member in the list *)
Inductive member_n (A : Type) : nat -> A -> list A -> Type :=
| mzero : forall elt tail, member_n O elt (elt :: tail)
| msucc : forall n elt h t, member_n n elt t -> member_n (S n) elt (h :: t).

Lemma member_n_tail_switch : forall A prefix n (elt : A) suffix suffix' ls',
  member_n n elt (prefix ++ suffix) -> n < length prefix ->
  prefix ++ suffix' = ls' -> member_n n elt ls'.
Proof.
  induction prefix; inversion 1; intros; subst; simpl in *; try omega; eauto.
Qed.

Lemma member_n_length : forall A n (elt : A) ls,
  member_n n elt ls -> n < length ls.
Proof.
  induction 1; simpl; omega.
Qed.

Inductive has_type : context -> expr -> type -> Prop :=
| T_Unit : forall ctx, has_type ctx UnitE UnitT
| T_Var : forall ctx n t, member_n n t ctx ->
                          has_type ctx (Var n) t 
| T_Abs : forall ctx t1 e t2, has_type (t1 :: ctx) e t2 ->
                              has_type ctx (Lam t1 e) (Arrow t1 t2)
| T_App : forall ctx e1 e2 t1 t2, has_type ctx e1 (Arrow t1 t2) ->
                                  has_type ctx e2 t1 ->
                                  has_type ctx (App e1 e2) t2.

(* Only closed terms can be inserted, so we don't have to worry about
   shifting indices. *)
Fixpoint subst (n : nat) (v e : expr) : expr :=
  match e with
    | UnitE => UnitE
    | Var n' => if eq_nat_dec n n' then v else e
    | Lam t e' => Lam t (subst (S n) v e')
    | App e1 e2 => App (subst n v e1) (subst n v e2)
  end.

(* Values are unit and abstractions. *)
Inductive value : expr -> Prop :=
| V_Unit : value UnitE
| V_Lam : forall t e, value (Lam t e).

(* Unsurprising evaluation relation: *)
Inductive eval : expr -> expr -> Prop := 
| E_App1 : forall e1 e1' e2, eval e1 e1' -> eval (App e1 e2) (App e1' e2)
| E_App2 : forall e1 e2 e2', value e1 -> eval e2 e2' -> eval (App e1 e2) (App e1 e2')
| E_AppAbs : forall t e v, value v -> eval (App (Lam t e) v) (subst 0 v e).

Example stlc_idu : has_type nil (Lam UnitT (Var 0)) (Arrow UnitT UnitT).
  auto.
Qed.

Example stlc_church_true :
  has_type nil (Lam UnitT (Lam UnitT (Var 1)))
               (Arrow UnitT (Arrow UnitT UnitT)).
  auto.
Qed.

Example stlc_app : has_type nil (App (App (Lam UnitT (Lam UnitT (Var 0)))
                                           UnitE) UnitE) UnitT.
  eauto 10.
Qed.

Lemma canonical_form_lam : forall v ctx t1 t2,
  has_type ctx v (Arrow t1 t2) -> value v -> exists e, v = Lam t1 e.
Proof.
  inversion 1; inversion 1; eauto; congruence.
Qed.

(* "All closed terms are values or can step"

   Induction works better without constants in its types, so we use an equality
   ctx = nil to assert that the term is closed *)
Lemma progress : forall ctx e t,
  ctx = nil -> has_type ctx e t -> (value e \/ exists e', eval e e').
Proof.
  (* Hint: My proof required 3 "Extern" hints, one of which applied
           canonical_form_lam in just the right way. *)
  induction 2; subst; intuition; eauto 6.  
Qed.

(* To build up to the substitution lemma, we need to prove a number of
   technical lemmas first. *)

(* "bounded n e" means that e is well scoped in a context containing n
   variables *)
Inductive bounded : nat -> expr -> Prop :=
| B_Unit : forall n, bounded n UnitE
| B_Var : forall n n', n < n' -> bounded n' (Var n)
| B_Lam : forall n t e, bounded (S n) e -> bounded n (Lam t e)
| B_App : forall n e1 e2, bounded n e1 -> bounded n e2 -> bounded n (App e1 e2).

(* "A term with type t bounded by n retains its type in a new context that
    differs only in the part excluding the first n elements." *)
Lemma bounded_term_context_switch :
  forall ctx e t, has_type ctx e t ->
  forall n prefix suffix ctx' suffix',
  bounded n e ->
  ctx = prefix ++ suffix ->
  ctx' = prefix ++ suffix' ->
  length prefix = n ->
  has_type ctx' e t.
Proof.
  (* Note the "eauto using app_comm_cons" below. Oddly, this proof did not
     work for me when app_comm_cons was added to the hint database. Bonus
     points for someone who can tell me why. *)
  induction 1; inversion 1; intros; subst; eauto using app_comm_cons.
Qed.

Lemma context_bounds_term : forall ctx e t,
  has_type ctx e t -> bounded (length ctx) e.
Proof.
  induction 1; eauto.
Qed.

(* "A term that is well-typed in the empty context is well-typed (at the same
    type) in any context." *)
Lemma closed_term_weakening : forall e t,
  has_type nil e t -> forall ctx, has_type ctx e t.
Proof.
  (* Exercise: Why do we need eauto twice here? And, relatedly, why do we
     explicitly need to apply bounded_term_context_switch? *)
  intros; eapply bounded_term_context_switch; eauto; eauto.
Qed.

Lemma member_n_last : forall A (ls : list A) elt elt',
  member_n (length ls) elt (ls ++ elt' :: nil) -> elt = elt'.
Proof.
  induction ls; inversion 1; simpl; auto.
Qed.

(* Like subst, but it handles the case where the variable is on the
   right-hand-side of the equality. *)
Ltac gen_subst :=
  repeat match goal with
           | [ H1 : ?x = ?rhs1, H2 : ?x = ?rhs2 |- _ ] => rewrite H1 in H2
         end;
  subst.

(* "If Γ,t' ⊢ e : t and · ⊢ v : t', then Γ ⊢ e[(length Γ) ↦ v] : t *)
Lemma substitution :
  forall ctx e t, has_type ctx e t ->
  forall ctx' t', ctx = ctx' ++ t' :: nil ->
  forall n, n = length ctx' ->
  forall v, value v ->
  has_type nil v t' ->
  has_type ctx' (subst n v e) t.
Proof.
  induction 1; simpl; intros; subst; eauto.
  match goal with
    | [ |- context[eq_nat_dec ?a ?b] ] => destruct (eq_nat_dec a b)
  end; eauto.
Qed.

(* If e has type t and steps to e', then e' has type t. *)
Lemma preservation : forall ctx e t,
  has_type ctx e t -> forall e', ctx = nil -> eval e e' -> has_type nil e' t.
Proof.
  induction 1; inversion 2; subst;
  match goal with
    | [ H : has_type _ _ (Arrow _ _) |- _ ] => inversion H
  end; eauto.
Qed.

(* The reflexive transitive closure of some relation *)
Inductive refl_trans A (R : A -> A -> Prop) : A -> A -> Prop :=
| refl : forall a, refl_trans R a a
| trans : forall a b c, R a b -> refl_trans R b c -> refl_trans R a c.

(* If · ⊢ e : t and e →* e', then e' is a value or e' can step *)
Theorem type_safety : forall e e' t, 
  refl_trans eval e e' -> has_type nil e t -> value e' \/ exists e'', eval e' e''.
Proof.
  induction 1; eauto.
Qed.

End STLC.