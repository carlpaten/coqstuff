Require Import List.
Require Import CpdtTactics MoreSpecif.

Set Implicit Arguments.

Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

Ltac prove_even := repeat constructor.

Theorem even_256 : isEven 256.
  prove_even.
Qed.

Print even_256.

Definition paartial := partial.

Print partial.
Local Open Scope partial_scope.

Definition check_even : forall n : nat, [isEven n].
  Hint Constructors isEven.

  refine (fix F (n : nat) : [isEven n] :=
    match n with
      | 0 => Yes
      | 1 => No
      | S (S n') => Reduce (F n')
    end); auto.
Defined.

Definition partialOut (P : Prop) (x : [P]) :=
  match x return (match x with
                    | Proved _ => P
                    | Uncertain => True
                  end) with
    | Proved pf => pf
    | Uncertain => I
  end.

Ltac prove_even_reflective :=
  match goal with
    | [ |- isEven ?N] => exact (partialOut (check_even N))
  end.

Theorem even_256' : isEven 256.
  prove_even_reflective.
Qed.

Print even_256'.

Theorem even_255 : isEven 255.
 (*  prove_even_reflective. *)
 (*   exact (partialOut (check_even 255)).  *)
Abort.

(* Proof search process within Gallina, Ltac to translate goal to use check_even *)

(* Exercise (45'): Reflective Collatz Conjecture *)

(* Back in Daniel's HW4 we saw the Collatz Conjecture *)

Require Import Arith.
Require Import Arith.Even.
Require Import Arith.Div2.

Section Collatz'.  
  
  (* Consider the following inductive definition of collatz_step and
  collatz_cycles. *)

  Inductive collatz_step' : nat -> nat -> Prop :=
  | ceven' : forall n, even n -> collatz_step' n (div2 n)
  | codd'  : forall n, odd n  -> collatz_step' n (3 * n + 1).

  Inductive collatz_cycles' : nat -> Prop :=
  | cone'   : collatz_cycles' 1
  | ccycle' : forall n, 
               (forall n', collatz_step' n n' -> collatz_cycles' n') -> 
               collatz_cycles' n.

  (* TODO: Try to apply the same methodology to create a similar 
     prove_collatz reflective tactic. Where are you stuck? *)

End Collatz'.

Section Collatz.
  (* To overcome that obstacle, consider the following inductive definition 
     of collatz_cycles, that denotes whether the "collatz process" terminates
     in no more than [step] steps. *)

  Inductive collatz_step : nat -> nat -> Prop :=
  | ceven : forall n, even n -> collatz_step n (div2 n)
  | codd  : forall n, odd n  -> collatz_step n (3 * n + 1).

  Inductive collatz_cycles : nat -> nat -> Prop :=
  | cone   : forall step, collatz_cycles step 1
  | ccycle : forall step n, 
               (forall n', collatz_step n n' -> collatz_cycles step n') -> 
               collatz_cycles (S step) n.

  (* TODO : Apply the same methodology to create a prove_collatz reflective
     tactic *)
  Definition check_collatz : forall (step n : nat), [collatz_cycles step n].
    (* TODO: Fill me *)
  Admitted.

  Ltac prove_collatz_reflective :=
    (* TODO: Fill me! *)
    idtac.

  (* TODO: When done uncomment and make sure they go through 
  Theorem c5 : collatz_cycles 5 5.
    prove_collatz_reflective.
  Qed.

  Theorem c42 : collatz_cycles 21 42.
    prove_collatz_reflective.
  Qed. 
  
  Print c42.
  *)

  (* Notice the change in proof sizes (and possibly running time since here we
     have a partial decision procedure - depending on your previous
     implementation) between this and HW 4 ! *) 
End Collatz.

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
  tauto.
Qed.

Definition tg := (and_ind, or_introl).

Print true_galore.

(* Inductive type *)

Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

(* Reflect back to Prop *)

Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

Theorem tautTrue : forall t, tautDenote t.
  induction t; crush.
Qed.

(* Reify *)

Ltac tautReify P :=
  match P with
    | True => TautTrue
    | ?P1 /\ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautAnd t1 t2)
    | ?P1 \/ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautOr t1 t2)
    | ?P1 -> ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautImp t1 t2)
  end.

Ltac obvious :=
  match goal with
    | [ |- ?P ] =>
      let t := tautReify P in
        exact (tautTrue t)
  end.

Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
  obvious.
Qed.

Print true_galore'.

(** * A Monoid Expression Simplifier *)

Section monoid.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A -> A.

  Infix "+" := f.

  Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
  Hypothesis identl : forall a, e + a = a.
  Hypothesis identr : forall a, a + e = a.

  (* Var case : what we can't model *)

  Inductive mexp : Set :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  Fixpoint mdenote (me : mexp) : A :=
    match me with
      | Ident => e
      | Var v => v
      | Op me1 me2 => mdenote me1 + mdenote me2
    end.

  (* Normalize by flattening *)
  Fixpoint flatten (me : mexp) : list A :=
    match me with
      | Ident => nil
      | Var x => x :: nil
      | Op me1 me2 => flatten me1 ++ flatten me2
    end.

  (* Denotation of normalized *)
  Fixpoint mldenote (ls : list A) : A :=
    match ls with
      | nil => e
      | x :: ls' => x + mldenote ls'
    end.

  (* Correctness *)

  Lemma flatten_correct' : forall ml2 ml1,
    mldenote ml1 + mldenote ml2 = mldenote (ml1 ++ ml2).
    induction ml1; crush.
  Qed.

  Theorem flatten_correct : forall me, mdenote me = mldenote (flatten me).
    Hint Resolve flatten_correct'.

    Print HintDb core.

    induction me; crush.
  Qed.

  Print HintDb core.
  Remove Hints flatten_correct'.
  Print HintDb core.

  (* Main theorem *)
  Theorem monoid_reflect : forall me1 me2,
    mldenote (flatten me1) = mldenote (flatten me2)
    -> mdenote me1 = mdenote me2.
    intros; repeat rewrite flatten_correct; assumption.
  Qed.

  Ltac reify me :=
    match me with
      | e => Ident
      | ?me1 + ?me2 =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          constr:(Op r1 r2)
      | _ => constr:(Var me)
    end.

  (* Final tactic *)
  Ltac monoid :=
    match goal with
      | [ |- ?me1 = ?me2 ] =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          change (mdenote r1 = mdenote r2);
            apply monoid_reflect; simpl
    end.


  Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
    intros; monoid.
    reflexivity.
  Qed.

  Print t1.
  
  (* Exercise (60') : Ordered + Commutative monoids *)

  (* Extend this section to represent ordered and commutative monoids *)
  Hypothesis comm  : forall a b, a + b = b + a.
  Hypothesis le : A -> A -> bool.

  (* TODO: Write Necessary Lemmas / Fixpoints *)

  Ltac ocmonoid := 
    (* TODO: Fill me when you are finished - this should be the 
       equivalent of the monoid tactic *)
    idtac.

  (* Example Revisited *)
  Section example.
    
    Variable a b c : A.
    (* This is to model an actual ordering between our elements *)
    Hypothesis l1 : le a b = true.
    Hypothesis l2 : le a c = true.
    Hypothesis l3 : le b c = true.
    Hypothesis l4 : le b a = false.
    Hypothesis l5 : le c a = false.
    Hypothesis l6 : le c b = false.

    Theorem t1' : a + (b + c) = b + (a + c).
      intros; ocmonoid.

      (* Since we don't have a concrete le function, reduction can't proceed 
         past any (le x y). We can go over that using the following process -
         unless your tactic doesn't use the ordering in a critical way *)

      Ltac simpl_le :=
        match goal with
          | [ H : le ?A ?B = ?X |- context[le ?A ?B] ] => rewrite H; simpl
        end.

      repeat simpl_le.

      reflexivity.
    Qed.
    
  End example.

End monoid.


(** * A Smarter Tautology Solver *)

Require Import Quote.
Print Quote.

Inductive formula : Set :=
| Atomic : index -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.

(* Wrapper of implication *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).

(** Now we can define our denotation function. *)

Definition asgn := varmap Prop.

Check varmap_find.
(* Print varmap_find. *)
Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => varmap_find False v atomics
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
    | Imp f1 f2 => formulaDenote atomics f1 --> formulaDenote atomics f2
  end.

Section my_tauto.
  Variable atomics : asgn.

  Definition holds (v : index) := varmap_find False v atomics.

  (* View of Lists as Sets *)
  Require Import ListSet.

  Definition index_eq : forall x y : index, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition add (s : set index) (v : index) := set_add index_eq v s.

  Definition In_dec : forall v (s : set index), {In v s} + {~ In v s}.
    Local Open Scope specif_scope.

    intro; refine (fix F (s : set index) : {In v s} + {~ In v s} :=
      match s with
        | nil => No
        | v' :: s' => index_eq v' v || F s'
      end); crush.
  Defined.

  Fixpoint allTrue (s : set index) : Prop :=
    match s with
      | nil => True
      | v :: s' => holds v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> holds v
    -> allTrue (add s v).
    induction s; crush;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; crush.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> varmap_find False v atomics.
    induction s; crush.
  Qed.

  Hint Resolve allTrue_add allTrue_In.

  Local Open Scope partial_scope.

  (* Deconstruction of hypotheses (goal) (assumptions) (hypothesis) (contiuation) *)
  Definition forward : forall (f : formula) (known : set index) (hyp : formula)
    (cont : forall known', [allTrue known' -> formulaDenote atomics f]),

    [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f].

    refine (fix F (f : formula) (known : set index) (hyp : formula)
      (cont : forall known', [allTrue known' -> formulaDenote atomics f])
      : [allTrue known -> formulaDenote atomics hyp -> formulaDenote atomics f] :=

      match hyp with
        | Atomic v => Reduce (cont (add known v))
        | Truth => Reduce (cont known)
        | Falsehood => Yes
        | And h1 h2 =>
          Reduce (F (Imp h2 f) known h1 (fun known' =>
            Reduce (F f known' h2 cont)))
        | Or h1 h2 => F f known h1 cont && F f known h2 cont
        | Imp _ _ => Reduce (cont known)
      end); crush.
  Defined.

  (* Analysis of final goal *)
  Definition backward : forall (known : set index) (f : formula),

    [allTrue known -> formulaDenote atomics f].

    refine (fix F (known : set index) (f : formula)
      : [allTrue known -> formulaDenote atomics f] :=

      match f with
        | Atomic v => Reduce (In_dec v known)
        | Truth => Yes
        | Falsehood => No
        | And f1 f2 => F known f1 && F known f2
        | Or f1 f2 => F known f1 || F known f2
        | Imp f1 f2 => forward f2 known f1 (fun known' => F known' f2)
      end); crush; eauto.
  Defined.

  (* Partial decision procedure *)

  Definition my_tauto : forall f : formula, [formulaDenote atomics f].
    intro; refine (Reduce (backward nil f)); crush.
  Defined.

End my_tauto.

Ltac my_tauto :=
  (* intro all quantifiers that do not bind Props *)
  repeat match goal with
           | [ |- forall x : ?P, _ ] =>
             match type of P with
               | Prop => fail 1
               | _ => intro
             end
         end;
  (* Reification via quote *)
  quote formulaDenote;
  (* exact + partial out *)
  match goal with
    | [ |- formulaDenote ?m ?f ] => exact (partialOut (my_tauto m f))
  end.

Theorem mt1 : True.
  my_tauto.
Qed.

Print mt1.

Theorem mt2 : forall x y : nat, x = y --> x = y.
  my_tauto.
Qed.

Definition nvm := (Node_vm, Empty_vm, End_idx, Left_idx, Right_idx).

Print mt2.

Theorem mt3 : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  --> y > z /\ (x < y \/ x < S y).
  my_tauto.
Qed.

Print mt3.

Theorem mt4 : True /\ True /\ True /\ True /\ True /\ True /\ False --> False.
  my_tauto.
Qed.

Print mt4.

Theorem mt4' : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
  tauto.
Qed.

Print mt4'.

(* Do quote manually *)

(* Duplicate free list of to-be-encoded values *)
Ltac inList x xs :=
  match xs with
    | tt => false
    | (x, _) => true
    | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
    match b with
      | true => xs
      | false => constr:(x, xs)
    end.

(*constr: is an annotation that indicates that the ltac term being modified must be treated like a Coq term *)

Ltac allVars xs e :=
  match e with
    | True => xs
    | False => xs
    | ?e1 /\ ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | ?e1 \/ ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | ?e1 -> ?e2 =>
      let xs := allVars xs e1 in
        allVars xs e2
    | _ => addToList e xs
  end.

(** We will also need a way to map a value to its position in a list. *)

Ltac lookup x xs :=
  match xs with
    | (x, _) => O
    | (_, ?xs') =>
      let n := lookup x xs' in
        constr:(S n)
  end.

(* Reification - partial *)

Inductive formula' : Set :=
| Atomic' : nat -> formula'
| Truth' : formula'
| Falsehood' : formula'
| And' : formula' -> formula' -> formula'
| Or' : formula' -> formula' -> formula'
| Imp' : formula' -> formula' -> formula'.

(* No -> wrapper needed! *)

Ltac reifyTerm xs e :=
  match e with
    | True => constr:Truth'
    | False => constr:Falsehood'
    | ?e1 /\ ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(And' p1 p2)
    | ?e1 \/ ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(Or' p1 p2)
    | ?e1 -> ?e2 =>
      let p1 := reifyTerm xs e1 in
      let p2 := reifyTerm xs e2 in
        constr:(Imp' p1 p2)
    | _ =>
      let n := lookup e xs in
        constr:(Atomic' n)
  end.

(** Finally, we bring all the pieces together. *)

Ltac reify :=
  match goal with
    | [ |- ?G ] => let xs := allVars tt G in
      let p := reifyTerm xs G in
        pose p
  end.

(** A quick test verifies that we are doing reification correctly. *)

Theorem mt3' : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  -> y > z /\ (x < y \/ x < S y).
  do 3 intro; reify.

Abort.

(* Quantifiers + Function Abstractions 
   -> Referencing different sets of free variables *)

Inductive type : Type :=
| Nat : type
| NatFunc : type -> type.

Inductive term : type -> Type :=
| Const : nat -> term Nat
| Plus : term Nat -> term Nat -> term Nat
| Abs : forall t, (nat -> term t) -> term (NatFunc t).

Fixpoint typeDenote (t : type) : Type :=
  match t with
    | Nat => nat
    | NatFunc t => nat -> typeDenote t
  end.

Fixpoint termDenote t (e : term t) : typeDenote t :=
  match e with
    | Const n => n
    | Plus e1 e2 => termDenote e1 + termDenote e2
    | Abs _ e1 => fun x => termDenote (e1 x)
  end.

(* Naive 1 *)

Ltac refl' e :=
  match e with
    | ?E1 + ?E2 =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(Plus r1 r2)

    | fun x : nat => ?E1 =>
      let r1 := refl' E1 in
        constr:(Abs (fun x => r1 x))

    | _ => constr:(Const e)
  end.

(* ?X matches terms that do not mention new variables *)

(* Pattern @?X, allows to mention newly introduced variables *)

Reset refl'.
Ltac refl' e :=
  match e with
    | ?E1 + ?E2 =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(Plus r1 r2)

    | fun x : nat => @?E1 x =>
      let r1 := refl' E1 in
        constr:(Abs r1)

    | _ => constr:(Const e)
  end.

(* Problem? Infinite recursion... *)

(* Every input to refl' should be a function over the values of variables introduced during recursion *)

Reset refl'.
Ltac refl' e :=
  match eval simpl in e with
    | fun x : ?T => @?E1 x + @?E2 x =>
      let r1 := refl' E1 in
      let r2 := refl' E2 in
        constr:(fun x => Plus (r1 x) (r2 x))

    | fun (x : ?T) (y : nat) => @?E1 x y =>
      let r1 := refl' (fun p : T * nat => E1 (fst p) (snd p)) in
        constr:(fun x => Abs (fun y => r1 (x, y)))

    | _ => constr:(fun x => Const (e x))
  end.

(* Downside (?), everything is in terms of functions...*)
(* Abstraction: Introduce new variable extending the type to T * nat *)
(* Notice the extra simpl reduction - packaging doesn't interfere with pattern matching... *)

Ltac refl :=
  match goal with
    | [ |- ?E1 = ?E2 ] =>
      let E1' := refl' (fun _ : unit => E1) in
      let E2' := refl' (fun _ : unit => E2) in
        change (termDenote (E1' tt) = termDenote (E2' tt));
          cbv beta iota delta [fst snd]
  end.

Goal (fun (x y : nat) => x + y + 13) = (fun (_ z : nat) => z).
  refl.
Abort.

(* Optional Exercise : If you found the previous exercise too unchallenging, 
   here is the closing paragraph from Adam's CPDT :

(** Our encoding here uses Coq functions to represent binding within the terms we reify, which makes it difficult to implement certain functions over reified terms.  An alternative would be to represent variables with numbers.  This can be done by writing a slightly smarter reification function that identifies variable references by detecting when term arguments are just compositions of [fst] and [snd]; from the order of the compositions we may read off the variable number.  We leave the details as an exercise for the reader. *)

  TODO: "exercise for the reader" *)