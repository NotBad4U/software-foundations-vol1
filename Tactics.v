Set Warnings "-notation-overridden,-parsing".

From LF Require Export Induction.
From LF Require Export Poly.

(* The apply Tactic *)

Theorem silly1 : forall (n m o p : nat),
     n = m ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.


Theorem silly2 : forall (n m o p : nat),
     n = m ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     oddb 3 = true ->
     evenb 4 = true.
Proof.
intros cond res.
apply res.
Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = (n =? 5) ->
     (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem rev_exercise1 : forall(l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
intros l l' H.
rewrite -> H.
Search "rev".
symmetry.
apply rev_involutive.
Qed.

(* The apply with Tactic *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
intros n m o p H H2.
rewrite H2.
apply H.
Qed.

(* The injection and discriminate Tactics *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. reflexivity.
Qed.

Theorem S_injective' :  forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H.
  intro.
  apply H0.
Qed.


Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros Hmo Hno.
  rewrite Hmo.
  rewrite Hno.
  reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. Qed.


Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H2.
  intros H3 h4.
  rewrite h4.
  reflexivity.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - intros H. reflexivity.
  - simpl.
    intros contradiction.
    discriminate contradiction.
Qed.


Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
intros X x y z l H H1.
discriminate H1.
Qed.


Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.


Theorem S_inj : forall (n m : nat) (b : bool),
     eqb (S n) (S m) = b  ->
     eqb n m = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

(* Using Tactics on Hypotheses *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
intros n.
induction n as [| n'].
- intros m H.
  simpl in H.
  destruct m.
  reflexivity.
  discriminate.
- Search "plus_n_Sm".
  intros m H. destruct m as [|m'].
    + discriminate H.
    + rewrite <- plus_n_Sm in H.
    rewrite <- plus_n_Sm in H.
    injection H.
    intro.
    apply IHn' in H0.
    rewrite -> H0.
    reflexivity.
Qed.

(* Varying the Induction Hypothesis *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) apply f_equal.
Abort.

Theorem double_injective: forall n m,
         double n = double m -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m eq. destruct m as [| m'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros m eq.
    destruct m as [| m'] eqn:E.
    + discriminate eq.
    + apply f_equal.
     apply IHn'.
     injection eq as goal.
     apply goal.
Qed.

Theorem eqb_true : forall n m,
    n =? m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  + intros m. destruct m as [| m'] eqn: E.
    - reflexivity.
    - intro. discriminate.
  + intros m eq.
    destruct m as [| m'] eqn: E.
    - discriminate.
    - apply IHn' in eq.
      rewrite eq.
      reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) apply f_equal.
    apply IHm'. injection eq as goal. apply goal.
Qed.

(* to be review *)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
intros n X l.
  generalize dependent n.
 induction l as [| l'].
- reflexivity.
- intros n H.
    induction n as [| n'].
    + inversion H.
    + apply S_injective in H. apply IHl in H. apply H.
Qed.


(* Unfolding Definitions *)

Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
    rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H.
  rewrite mult_assoc.
  reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.


Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m  eqn:E.
  - simpl.
  reflexivity.
  - simpl.
    reflexivity.
Qed.


(* Using destruct on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
intros n.
unfold sillyfun.
destruct (n =? 3).
- reflexivity.
- destruct (n =? 5).
  + reflexivity.
  + reflexivity.
Qed.


Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].

    intros l1 l2 eq. inversion eq. reflexivity.

    simpl. destruct (split l') as [l1' l2'].
    intros l1 l2 eq. inversion eq.
    simpl. apply f_equal. apply IHl'. reflexivity.  Qed.

Theorem combine_split' : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  - intros l1 l2 H.
    injection H.
    intros.
    rewrite <- H0.
    rewrite <- H1.
    reflexivity.
  - simpl.
    destruct (split l') as [x' y'] eqn: E.
    intros l1 l2 eq.
    injection eq.
    simpl.
    intros Hl2 Hl1.
    rewrite <- Hl1.
    rewrite <- Hl2.
    simpl; rewrite IHl'.
    + reflexivity.
    + reflexivity.
Qed.


Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.


Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  apply eqb_true in Heqe3.
  rewrite -> Heqe3. reflexivity.
  destruct (n =? 5) eqn:Heqe5.
  apply eqb_true in Heqe5.
  rewrite -> Heqe5. reflexivity.
  discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
intros.
destruct (f b) eqn: HFB.
- destruct b eqn: HB.
  + rewrite HFB. apply HFB.
  + destruct (f true) eqn: HT.
    *  apply HT.
    * apply HFB.
- destruct b.
  + destruct (f false) eqn:HF.
    * apply HFB.
    * apply HF.
  + rewrite HFB; apply HFB.
Qed.

(* Additional Exercises *)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
intros n m.
destruct (m =? n) eqn: HNM.
apply eqb_true in HNM.
rewrite HNM.
Search "eqb_sym_informal".
symmetry.
apply eqb_nat_refl.
Abort.

