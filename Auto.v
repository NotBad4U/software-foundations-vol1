Set Warnings "-notation-overridden,-parsing".
From Coq Require Import omega.Omega.
From LF Require Import Maps.
From LF Require Import Imp.

(* First, define a little Ltac macro to compress a common pattern into a single command.*)
Ltac inv H := inversion H; subst; clear H.

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inv E2.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; apply H1. }
    subst st'0.
    apply IHE1_2. assumption.
  (* E_IfTrue *)
  - (* b evaluates to true *)
    apply IHE1. assumption.
  - (* b evaluates to false (contradiction) *)
    rewrite H in H5. inversion H5.
  (* E_IfFalse *)
  - (* b evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* b evaluates to false *)
    apply IHE1. assumption.
  (* E_WhileFalse *)
  - (* b evaluates to false *)
    reflexivity.
  - (* b evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
Qed.

(* The auto Tactic *)

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.

Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.

(**
  The auto tactic solves goals that are solvable by any combination of
  intros and
  apply (of hypotheses from the local context, by default).

  Using auto is always "safe" in the sense that it will never fail and will never change the proof state:
  either it completely solves the current goal, or it does nothing.
*)

Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P->Q) -> (P->S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  (* When it cannot solve the goal, [auto] does nothing *)
  auto.
  (* Optional argument says how deep to search (default is 5) *)
  auto 6.
Qed.

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.

Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. omega. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.

Hint Resolve le_antisym.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  intros.
  auto. (* picks up hint from database *)
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  (* does nothing *)
Abort.

Hint Unfold is_fortytwo.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. (* try also: info_auto. *)
Qed.

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
       induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
Qed.


(** When we are using a particular tactic many times in a proof, we
    can use a variant of the [Proof] command to make that tactic into
    a default within the proof.  Saying [Proof with t] (where [t] is
    an arbitrary tactic) allows us to use [t1...] as a shorthand for
    [t1;t] within the proof.  As an illustration, here is an alternate
    version of the previous proof, using [Proof with auto]. *)

Theorem ceval_deterministic'_alt: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inversion E2; subst...
  - (* E_Seq *)
    assert (st' = st'0) as EQ1...
    subst st'0...
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H5. discriminate.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rewrite H in H2. discriminate.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rewrite H in H4. discriminate.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1...
    subst st'0...
Qed.


(* Searching For Hypotheses *)


Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_IfTrue *)
    + (* b evaluates to false (contradiction) *)
      rwd H H5.
  - (* E_IfFalse *)
    + (* b evaluates to true (contradiction) *)
      rwd H H5.
  - (* E_WhileFalse *)
    + (* b evaluates to true (contradiction) *)
      rwd H H2.
  (* E_WhileTrue *)
  - (* b evaluates to false (contradiction) *)
    rwd H H4.
  - (* b evaluates to true *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto. Qed.


Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
  end.


Theorem ceval_deterministic''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd; auto.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1 by auto.
    subst st'0.
    auto.
  - (* E_WhileTrue *)
    + (* b evaluates to true *)
      assert (st' = st'0) as EQ1 by auto.
      subst st'0.
      auto. Qed.

Theorem ceval_deterministic'''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd; auto.
  - (* E_Seq *)
    rewrite (IHE1_1 st'0 H1) in *. auto.
  - (* E_WhileTrue *)
    + (* b evaluates to true *)
      rewrite (IHE1_1 st'0 H3) in *. auto. Qed.

Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.

Theorem ceval_deterministic''''': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd;
    repeat find_eqn; auto.
Qed.

Module Repeat.

Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).


(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'SKIP'" :=
   CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).
Notation "'REPEAT' c 'UNTIL' b 'END'" :=
  (CRepeat c b) (at level 80, right associativity).

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st  =[ WHILE b DO c END ]=> st''
  | E_RepeatEnd : forall st st' b c,
      st  =[ c ]=> st' ->
      beval st' b = true ->
      st  =[ REPEAT c UNTIL b END ]=> st'
  | E_RepeatLoop : forall st st' st'' b c,
      st  =[ c ]=> st' ->
      beval st' b = false ->
      st' =[ REPEAT c UNTIL b END ]=> st'' ->
      st  =[ REPEAT c UNTIL b END ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

(** Our first attempt at the determinacy proof does not quite succeed:
    the [E_RepeatEnd] and [E_RepeatLoop] cases are not handled by our
    previous automation. *)

Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; try find_rwd; repeat find_eqn; auto.
  - (* E_RepeatEnd *)
    + (* b evaluates to false (contradiction) *)
       find_rwd.
       (* oops: why didn't [find_rwd] solve this for us already?
          answer: we did things in the wrong order. *)
  - (* E_RepeatLoop *)
     + (* b evaluates to true (contradiction) *)
        find_rwd.
Qed.

(** Fortunately, to fix this, we just have to swap the invocations of
    [find_eqn] and [find_rwd]. *)

Theorem ceval_deterministic': forall c st st1 st2,
    st =[ c ]=> st1  ->
    st =[ c ]=> st2 ->
    st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1;
    intros st2 E2; inversion E2; subst; repeat find_eqn; try find_rwd; auto.
Qed.

End Repeat.

Example ceval_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  (* We supply the intermediate state [st']... *)
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

Example ceval'_example1:
  empty_st =[
    X ::= 2;;
    TEST X <= 1
      THEN Y ::= 3
      ELSE Z ::= 4
    FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  eapply E_Seq. (* 1 *)
  - apply E_Ass. (* 2 *)
    reflexivity. (* 3 *)
  - (* 4 *) apply E_IfFalse. reflexivity. apply E_Ass. reflexivity.
Qed.

Hint Constructors ceval.
Hint Transparent state.
Hint Transparent total_map.

Definition st12 := (Y !-> 2 ; X !-> 1).
Definition st21 := (Y !-> 1 ; X !-> 2).

Example eauto_example : exists s',
  st21 =[
    TEST X <= Y
      THEN Z ::= Y - X
      ELSE Y ::= X + Z
    FI
  ]=> s'.
Proof. info_eauto. Qed.

(** The [eauto] tactic works just like [auto], except that it uses
    [eapply] instead of [apply]; [info_eauto] shows us which facts
    [auto] uses. *)

(** Pro tip: One might think that, since [eapply] and [eauto] are more
    powerful than [apply] and [auto], we should just use them all the
    time.  Unfortunately, they are also significantly slower --
    especially [eauto].  Coq experts tend to use [apply] and [auto]
    most of the time, only switching to the [e] variants when the
    ordinary variants don't do the job. *)