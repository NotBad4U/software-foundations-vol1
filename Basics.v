(* Data and Functions

The proofs of these claims were always the same:
use simpl to simplify both sides of the equation,
then use reflexivity to check that both sides contain identical values.
*)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | _, _ => true
end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Example test_nandb1: (nandb true false) = true.
Proof.
simpl. reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
simpl. reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
simpl. reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
simpl. reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1, b2, b3 with
  | true, true, true => true
  | _, _, _ => false
end.

Example test_andb31: (andb3 true true true) = true.
simpl. reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
simpl. reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
simpl. reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
simpl. reflexivity.
Qed.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.


Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

(*  factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0) *)

Fixpoint factorial (n:nat) : nat :=
match n with
| O => S O
| S p => mult n (factorial p)
end.


Compute (factorial 5).

Example test_factorial1: (factorial 3) = 6.
simpl. reflexivity.
Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
simpl. reflexivity.
Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.


Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Fixpoint ltb (n m : nat) : bool :=
  (leb n m) && (negb (eqb n m)).

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
simpl. reflexivity.
Qed.

Example test_ltb2: (ltb 2 4) = true.
simpl. reflexivity.
Qed.

Example test_ltb3: (ltb 4 2) = false.
simpl. reflexivity.
Qed.

(* Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity.
Qed.

(* Proof by Rewriting *)

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
intros n m H.
rewrite H.
reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
intros n m H.
simpl.
rewrite <- H.
reflexivity.
Qed.

(* Proof by Case Analysis 

The destruct generates two subgoals, which we must then prove, separately, in order to get Coq to accept the theorem.
The annotation "as [| n']" is called an intro pattern.
*)

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E. (* The eqn:E annotation tells destruct to give the name E to this equation.*)
  - reflexivity.
  - reflexivity. Qed.


Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c H.
destruct c eqn: E.
- reflexivity.
- rewrite <- H.
  + destruct b eqn: E2. reflexivity. reflexivity.
Qed.

Theorem andb_true_elim3 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  - destruct c.
    + reflexivity.
    + simpl. intros. assumption.
  - destruct c.
    + simpl. intros. reflexivity.
    + simpl. intros H. assumption.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros n.
  destruct n as [|n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.


Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
intros f H b.
destruct b.
- rewrite H. rewrite H. reflexivity.
- rewrite H. rewrite H. reflexivity.
Qed.


(* Prove the following theorem.
(Hint: This one can be a bit tricky, depending on how you approach it.
You will probably need both destruct and rewrite,
but destructing everything in sight is not the best way. *)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
intros b c.
destruct b.
- simpl. intro. rewrite H. reflexivity.
- simpl. intro. rewrite H. reflexivity.
Qed.


Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
match m with
| Z => B Z
| B z => A (B z)
| A n => A (A n)
end.


Fixpoint bin_to_nat (m:bin): nat :=
match m with
| Z => O
| B z => S (bin_to_nat z)
| A n => S (bin_to_nat n)
end.



Definition bar: nat := 1.



