Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.


(** Inductively Defined Propositions *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).



Theorem ev_double : forall n, even (double n).
Proof.
intros n.
induction n as [|n' IHn'].
- simpl.
  apply ev_0.
- simpl.
  apply ev_SS.
  assumption.
Qed.

(* Using Evidence in Proofs *)


Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem a : forall n, even (S (S n)) -> even n.
Proof.
intros n E.
destruct E as [| n' E'].
Abort.

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm as Heq.
   rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~even 1.
  intros H. inversion H.
Qed.

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
intros n E.
inversion E.
apply evSS_ev in H0.
assumption.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
intro E.
inversion E.
inversion H0.
inversion H2.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [|n' E'].
  - exists 0. reflexivity.
  - simpl.
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I.
Abort.

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
intros n m En Em.
induction En as [|n En' IH].
- simpl. assumption.
- simpl. apply ev_SS. apply IH.
Qed.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).


Theorem even'_ev : forall n, even' n <-> even n.
Proof.
intros n.
split.
- intro H. induction H.
  + apply ev_0.
  + apply ev_SS. apply ev_0.
  + apply ev_sum. apply IHeven'1. apply IHeven'2.
- intro H. induction H.
  + apply even'_0.
  + assert (plus_SSn: forall n: nat, S (S n) = n+2).
    { intro n'. induction n'. reflexivity. rewrite IHn'. reflexivity. }
    rewrite plus_SSn.
    apply even'_sum.
    * apply IHeven.
    * apply even'_2.
Qed.

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros n m Esum En.
  induction En as [|n' En' IHEn].
  - simpl in Esum. assumption.
  - inversion Esum.
    apply IHEn in H0.
    assumption.
Qed.

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
intros n m p H.
apply ev_sum with (n := n+m) (m := n+p) in H.
Admitted. (* just a chain of rewrite now *)


(* Inductive Relations *)

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).


Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2. Qed.


End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros.
  induction H0.
  + assumption.
  + apply le_S. assumption.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
intro n.
induction n.
apply le_n.
apply le_S.
assumption.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
intros n m H.
induction H.
apply le_n.
rewrite IHle.
apply le_S.
apply le_n.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
intros n m H.
inversion H.
- apply le_n.
- apply le_trans with (n := S n).
  + apply le_S. apply le_n.
  + apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
intros a b.
induction a.
- simpl. apply O_le_n.
- simpl.  apply n_le_m__Sn_le_Sm. assumption.
Qed.


Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros. unfold lt. unfold lt in H. induction H.
  - split.
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
  - split. destruct IHle.
    + apply le_trans with (n:= m).
      * apply H0.
      * apply le_S. apply le_n.
    + apply le_trans with (n:= m).
      * destruct IHle. apply H1.
      * apply le_S. apply le_n.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros. apply le_trans with (o:= S m) in H.
  + unfold lt. apply H.
  + apply le_S. apply le_n.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m H.
  generalize dependent n.
  induction m as [|m' IHm'].
  - destruct n.
    + intro. apply le_n.
    + simpl. intro. discriminate H.
  - destruct n as [|n'] eqn: E.
    + simpl. intro. apply O_le_n.
    + simpl. intro. apply IHm' in H. apply n_le_m__Sn_le_Sm. assumption.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
intros n m H.
    induction H as [| m' lnm IH].
  - induction n as [| n' IHn'].
    + reflexivity.
    + simpl. assumption.
  - induction n as [| n' IH'].
    + reflexivity.
    + destruct m' as [| m''] eqn: E.
       simpl in IH.
      * discriminate IH.
Admitted.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
intros n m o H H1.
apply leb_complete in H.
apply leb_complete in H1.
apply leb_correct.
apply le_trans with m.
- assumption.
- assumption.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  - intros. apply leb_complete in H. apply H.
  - intros. apply leb_correct. apply H.
Qed.

(* Case Study: Regular Expressions *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).


Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

