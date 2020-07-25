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
  apply (MChar 1).
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
apply (MApp [1] _ [2]).
apply (MChar 1).
apply (MChar 2).
Qed.

Example reg_exp_ex3 : ~([1; 2] =~ Char 1).
Proof.
unfold not.
intro H.
inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
match l with
| [] => EmptyStr
| x :: l' => App (Char x) (reg_exp_of_list l')
end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
simpl.
apply (MApp [1]).
apply MChar.
apply (MApp [2]).
apply MChar.
apply (MApp [3]).
apply MChar.
apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
intros T s re H.
rewrite <- (app_nil_r _ s).
apply (MStarApp s [] ).
- assumption.
- apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~(s =~ EmptySet).
Proof.
intros T s.
unfold not.
induction s as [|h' s' IHs'].
- intro H. inversion H.
- intro. apply IHs'. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
intros T s re1 re2 H.
destruct H.
- apply MUnionL.
  assumption.
- apply MUnionR.
  assumption.
Qed.


Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
intros T ss re H.
induction ss.
- simpl. apply MStar0.
- simpl. apply MStarApp.
  + apply H.
    simpl.
    left.
    reflexivity.
  + apply IHss.
    intros s H1.
    apply H.
    simpl.
    right.
    assumption.
Qed.


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
intros T s1 s2.
split.
- generalize dependent s1. induction s2 as [|s2' l IHs2].
  + intros s1 H.
    unfold reg_exp_of_list in H.
    inversion H.
    reflexivity.
  + intros. simpl in H.
    inversion H.
    apply IHs2 in H4.
    inversion H3.
    simpl.
    rewrite H4.
    reflexivity.
- intros H. generalize dependent s1. induction s2 as [|s2' l IHs2].
  + simpl. intros s1 H. rewrite H. apply MEmpty.
  + intros s1 H.
    rewrite H.
    simpl.
    Search "::".
    assert (HR: s2' :: l = [s2'] ++ l). { reflexivity. }
    rewrite HR.
    apply MApp.
    apply MChar.
    apply IHs2.
    reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
    s =~ re ->
    In x s ->
    In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
      | x'
      | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
      | s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
      | re|s1 s2 re Hmatch IH1 Hmatch2 IH2].
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
match re with
| EmptySet => false
| EmptyStr => true
| Char _ => true
| App x y => re_not_empty x && re_not_empty y
| Union x y => re_not_empty x || re_not_empty y
| Star re => true
end.

Theorem re_not_empty_r : forall T (re : @reg_exp T),
  re_not_empty re = true -> (exists s, s =~ re).
Proof.
intros T re H. induction re.
- simpl in H. discriminate.
- exists []. apply MEmpty.
- exists [t]. apply MChar.
- simpl in H. apply andb_true_iff in H.  inversion H. apply IHre1 in H0. apply IHre2 in H1.
  destruct H0. destruct H1. exists (x ++ x0). apply MApp.
   assumption. assumption.
- simpl in H. apply orb_true_iff in H. inversion H. apply IHre1 in H0. destruct H0. exists x. apply MUnionL. assumption.
  apply IHre2 in H0. destruct H0. exists x. apply MUnionR. assumption.
- exists []. apply MStar0.
Qed.

Theorem re_not_empty_l : forall T (re : @reg_exp T),
   (exists s, s =~ re) -> re_not_empty re = true.
Proof.
intros T re [s Hres]. induction Hres.
- reflexivity.
- reflexivity.
- simpl. apply andb_true_iff. split.
  + assumption.
  + assumption.
- simpl. apply orb_true_iff. left. assumption.
- simpl. apply orb_true_iff. right. assumption.
- reflexivity.
- assumption.
Qed.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
intros T re.
split.
apply re_not_empty_l.
apply re_not_empty_r.
Qed.

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *)  discriminate. (* can use try tactic here *)
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.
  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.


Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
intros T s re H.
remember (Star re) as re'.
induction H; try discriminate.
- inversion Heqre'. exists []. split.
  + simpl. reflexivity.
  + simpl. destruct s'.
    * intro. destruct H. (* contradiction *)
    * intro. destruct H. (* contradiction *)
- inversion Heqre'.
  apply IHexp_match2 in Heqre'.
  destruct Heqre'.
  exists ([s1] ++ x).
  destruct H1.
  simpl.
  rewrite H1.
  split.
  reflexivity.
  intros.
  destruct H4.
  + rewrite <- H4. rewrite H2 in H. assumption.
  + apply H3. auto.
Qed.

Module Pumping.
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
match re with
| EmptySet => 0
| EmptyStr => 1
| Char _ => 2
| App re1 re2 =>
    pumping_constant re1 + pumping_constant re2
| Union re1 re2 =>
    pumping_constant re1 + pumping_constant re2
| Star _ => 1
end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
match n with
| 0 => []
| S n' => l ++ napp n' l
end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s  ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Import Coq.omega.Omega.
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - simpl. omega.
Admitted.

End Pumping.


(* Case Study: Improving Reflection *)


Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqb n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.


Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.


Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
intros P b H.
destruct b.
- apply ReflectT. apply H. reflexivity.
- apply ReflectF. unfold not. intros. apply H in H0. discriminate.
Qed.

Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true). 
Proof.
  intros. split.
  - destruct H.
    + auto.
    + intros. unfold not in H. apply H in H0. inversion H0.
  - destruct H.
    + auto.
    + intros. inversion H0.
Qed.

Theorem reflect_iff' : forall P b, reflect P b -> (P <-> b = true).
Proof.
intros. split.
- destruct H.
  + intro. reflexivity.
  + unfold not in H. intro. apply H in H0. destruct H0.
- destruct H.
  + intro. assumption.
  + intro. discriminate H0.
Qed.

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
Proof.
  intros n l H.
  induction l as [|h t IH].
  - simpl. intros H'. apply H'.
  - simpl. destruct (eqbP h n).
    + intros H1. simpl in H.
      symmetry in H0.
      rewrite <- eqb_eq in H0.
      rewrite H0 in H.
      inversion H. 
    + intros H2. apply H0.
      destruct H2 as [H3|H3].
      * apply H3.
      * simpl in H.
        destruct (eqb n h).
        { inversion H. }
        { apply IH in H. exfalso.  apply H.  apply H3. }
Qed.

(* Additional Exercises *)
