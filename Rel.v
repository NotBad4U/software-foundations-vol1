Definition relation (X: Type) := X -> X -> Prop.

(* Basic Properties *)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
unfold partial_function.
intros x y1 y2 H1 H2.
inversion H1.
inversion H2.
reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~(partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. Qed.

Inductive total_relation (m n : nat) : Prop :=
| total_mn : total_relation m n.

Theorem total_relation_not_partial_function : ~(partial_function total_relation).
Proof.
unfold not.
unfold partial_function.
 intros HC.
  assert (0 = 1) as Nonsense.
  - apply HC with (x := 0).
    + apply total_mn.
    + apply total_mn.
  - discriminate Nonsense.
Qed.

Inductive empty_relation (m n : nat) : Prop :=.

Theorem empty_relation_not_partial_function : partial_function empty_relation.
Proof.
unfold partial_function.
intros.
inversion H.
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n. Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
intros n m o Hnm Hmo.
induction Hmo.
- (* le_n *) apply Hnm.
- (* le_S *) apply le_S. apply IHHmo. Qed.


Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o]; apply le_S; assumption.
Qed.



Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - inversion Hmo.
    + rewrite <- H0.
      apply le_S.
      apply Hnm.
    + apply le_S.
      apply IHo'.
      apply H0.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
intros n m H.
inversion H.
apply le_n.
apply le_Sn_le. apply H1.
Qed.

Theorem le_Sn_n : forall n,
  ~(S n <= n).
Proof.
intros n.
unfold not.
intro H.
induction n.
- inversion H.
- apply IHn.
  apply le_S_n.
  assumption.
Qed.


