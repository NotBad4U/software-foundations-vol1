Print LoadPath.

Require Import LF.Basics.

(* # Proof by Induction *)

(*
The principle of induction over natural numbers: If P(n) is some proposition involving a natural number n and we want to show that P holds for all numbers n, we can reason like this:
- show that P(O) holds;
- show that, for any n', if P(n') holds, then so does P(S n');
- conclude that P(n) holds for all n.

one where we must show P(O)
and another where we must show P(n') → P(S n').
*)

Theorem plus_n_O_secondtry : forall n : nat,
  n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
  intros n. induction n as [|n' IHn' ].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros n m. induction n as [|n' IHn' ].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
intros n m. induction n as [|n' IHn' ].
- apply plus_n_O.
- simpl. rewrite IHn'. apply plus_n_Sm.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p. induction n as [|n' IHn' ].
- reflexivity.
- simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


Lemma double_plus : forall n, double n = n + n .
Proof.
intros n. induction n as [|n' IHn' ].
{ simpl. reflexivity. }
{ simpl.
  rewrite plus_n_Sm.
  rewrite IHn'.
  rewrite plus_n_Sm.
  apply plus_n_Sm. }
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity.
Qed.


Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
intros n. induction n as [| n' IHn'].
- simpl. reflexivity.
- assert (H: evenb (S (S n')) = evenb n'). reflexivity.
  rewrite -> H.
  rewrite -> IHn'.
  rewrite negb_involutive.
  reflexivity.
Qed.

(*
La tactique induction peut être utilisée pour exprimer que l’on effectue
une preuve par récurrence sur une expression qui n’est pas encore dans le
contexte. En fait “ induction id ” est souvent équivalente à la tactique composée
“ intros until id; elim id ”.

Il est justifié d’utiliser cette tactique lorsque l’on veut rendre explicite le fait
que l’on fait une démonstration par récurrence par rapport à une variable quantifiée universellement :
le script de la preuve est alors très proche du texte que l’on écrirait pour exprimer comment la preuve s’effectue.
*)

(* # Proofs Within Proofs *)


Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.


Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H.
  reflexivity.
Qed.

(* # Formal vs. Informal Proof *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem eqb_nat_refl : forall n : nat,
  true = eqb n n.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. 
  (* I have used associativity to simplify the swapping done*)
  rewrite -> plus_assoc'. simpl. rewrite -> plus_assoc'.
  (* at this point using reflexivity fails even though it seems obvious
     may be becouse addition follows an associativity order. Hence it would be 
     useful to use commutativity now. 
  *)
  assert (H1: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H1.
  reflexivity.
Qed.

Theorem mult_n_Sm : forall m n : nat,
    n * (S m) = n + n * m.
Proof.
  intros n m. induction m.
  - reflexivity.
  - simpl. rewrite -> IHm. rewrite -> plus_swap. reflexivity.
Qed.




Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m. induction m.
  - simpl. rewrite -> mult_0_r. reflexivity.
  - simpl. rewrite -> mult_n_Sm. simpl. rewrite -> IHm. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed. 

Theorem order_indepent_mult : forall m n p : nat, n * p * m = m * n * p.
Proof.
  intros m n p. rewrite -> mult_comm. simpl. induction m as [|m' IHm'].
  - simpl. reflexivity.
  -  simpl. rewrite -> mult_plus_distr_r. rewrite -> IHm'. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros m n p.  induction n as [|n' IHn'].
  - simpl. rewrite <- mult_n_O. simpl. reflexivity.
  - simpl.  rewrite -> mult_comm.  rewrite -> mult_n_Sm. rewrite -> mult_plus_distr_r.  rewrite -> mult_plus_distr_r. 
  rewrite -> mult_comm. rewrite -> order_indepent_mult. reflexivity.
Qed.



