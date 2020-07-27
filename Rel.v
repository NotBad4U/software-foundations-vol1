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

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~(symmetric le).
Proof.
unfold not.
unfold symmetric.
intros.
assert (Nonsense: 1 <= 0).
{ apply (H 0). apply le_S. apply le_n. }
inversion Nonsense.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.


Theorem Sn_le_Sm__n_le_m: forall n m, n <= m -> S n <= S m.
Proof. intros. induction H. apply le_n. apply le_S. apply IHle. Qed.

Theorem le_contradiction: forall x y, x <= y -> y <= x -> False.
Admitted.


Theorem le_antisymmetric :
  antisymmetric le.
Proof.
unfold antisymmetric.
intros.
generalize dependent a.
induction b.
- intros. inversion H. reflexivity.
- intros. destruct a.
  + inversion H0.
  + apply le_contradiction in H.
    destruct H.
    apply H0.
Qed.

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
unfold lt.
intros.
apply le_S_n.
apply (le_trans (S n) m (S p)).
- assumption.
- assumption.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).
Theorem le_order :
  order le.
Proof.
  unfold order. split.
    - (* refl *) apply le_reflexive.
    - split.
      + (* antisym *) apply le_antisymmetric.
      + (* transitive. *) apply le_trans. Qed.


(* Reflexive, Transitive Closure *)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - (* -> *)
    intro H. induction H.
    + (* le_n *) apply rt_refl.
    + (* le_S *)
      apply rt_trans with m. apply IHle. apply rt_step.
      apply nn.
  - (* <- *)
    intro H. induction H.
    + (* rt_step *) inversion H. apply le_S. apply le_n.
    + (* rt_refl *) apply le_n.
    + (* rt_trans *)
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2. Qed.


Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. apply H. apply rt1n_refl. Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
intros.
induction H.
- assumption.
- apply rt1n_trans with y.
  apply Hxy.
  apply IHclos_refl_trans_1n.
  assumption.
Qed.


Theorem rtc_rsc_coincide :
        forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
intros.
split.
- intro H. induction H.
  + apply rt1n_trans with y.
    * assumption.
    * apply rt1n_refl.
  + apply rt1n_refl.
  + apply rsc_trans with y. assumption. assumption.
- intro H. induction H.
  + apply rt_refl.
  + apply rt_trans with y.
    * apply rt_step. apply Hxy.
    * apply IHclos_refl_trans_1n.
Qed.