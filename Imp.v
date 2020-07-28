Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.

From LF Require Import Maps.

(* Arithmetic and Boolean Expressions *)

(**
 a ::= nat
        | a + a
        | a - a
        | a * a
*)
Module AExp.
Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

(**

    b ::= true
        | false
        | a = a
        | a ≤ a
        | ¬b
        | b && b
*)
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
  reflexivity.
Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity. Qed.

(* Coq Automation *)

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1 eqn:Ea1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
intros. induction b;
  repeat (try (reflexivity));
  repeat (try (simpl; rewrite optimize_0plus_sound; rewrite optimize_0plus_sound; reflexivity)).
- simpl. rewrite IHb. reflexivity.
- simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).

End TooHardToRead.

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.


Reserved Notation "e '\\' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum (n : nat) :
    ANum n \\ n
| E_APlus {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 -> e2 \\ n2 -> APlus e1 e2 \\ n1 + n2
| E_AMinus {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 -> e2 \\ n2 -> AMinus e1 e2 \\ n1 - n2
| E_AMult {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 -> e2 \\ n2 -> AMult e1 e2 \\ n1 * n2

where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
split.
- intro H. induction H;
  repeat (try (simpl; subst; reflexivity)).
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Reserved Notation "e '\\\' b" (at level 90, left associativity).

Inductive bevalR : bexp -> bool -> Prop :=
| E_BTrue  : bevalR (BTrue) true
| E_BFalse : bevalR (BFalse) false
| E_BEq {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 -> e2 \\ n2 -> BEq e1 e2 \\\ n1 =? n2
| E_BLe {e1 e2 : aexp} {n1 n2 : nat} :
    e1 \\ n1 -> e2 \\ n2 -> BLe e1 e2 \\\ n1 <=? n2
| E_BNot {a1 : bexp} {b : bool} :
    a1 \\\ b -> BNot a1 \\\ negb b
| E_BAnd {a1 a2 : bexp} {b1 b2 : bool}:
    a1 \\\ b1 -> a2 \\\ b2 -> BAnd a1 a2 \\\ andb b1 b2

where "e '\\\' b" := (bevalR e b) : type_scope.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
split.
- intro H. induction H.
  + simpl. reflexivity.
  + simpl. reflexivity.
  + simpl. apply aeval_iff_aevalR in H. apply aeval_iff_aevalR in H0. subst. reflexivity.
  + simpl. apply aeval_iff_aevalR in H. apply aeval_iff_aevalR in H0. subst. reflexivity.
  + simpl. rewrite IHbevalR. reflexivity.
  + simpl. rewrite IHbevalR1. rewrite IHbevalR2. reflexivity.
- generalize dependent bv.
  induction b.
  + intros. subst. apply E_BTrue.
  + intros. subst. apply E_BFalse.
  + intros. subst. simpl. apply E_BEq.
    * apply aeval_iff_aevalR. reflexivity.
    * apply aeval_iff_aevalR. reflexivity.
  + intros. subst. constructor.
    * apply aeval_iff_aevalR. reflexivity.
    * apply aeval_iff_aevalR. reflexivity.
  +  intros. simpl in *. subst. constructor. apply IHb. reflexivity.
  +  intros. simpl in *. subst. constructor.
    * apply IHb1. reflexivity.
    * apply IHb2. reflexivity.
Qed.

End AExp.
