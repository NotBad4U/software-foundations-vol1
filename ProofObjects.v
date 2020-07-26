(* Proof Scripts *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).

Theorem ev_4 : even 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4': even 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.

Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Theorem ev_8 : even 8.
Proof.
apply ev_SS.
apply ev_SS.
apply ev_SS.
apply ev_SS.
apply ev_0.
Qed.

Definition ev_8' : even 8 :=
 ev_SS 6 ( ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).

(* Quantifiers, Implications, Functions *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, even n -> even (4 + n) :=
  fun (n : nat) => fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).


Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4'.
Check ev_plus4''.

Definition ev_plus2 : Prop :=
  forall n, forall (E : even n), even (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : even n), even (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, even n -> even (n + 2).

(* Programming with Tactics *)

(** 
  This feature is mainly useful for writing functions with dependent types,
  which we won't explore much further in this book.
  But it does illustrate the uniformity and orthogonality of the basic ideas in Coq.
*)

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n.
Defined.


(* Logical Connectives as Inductive Types *)

Module Props.

Module And.

Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.

End And.

Print prod.

Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R.
intros p Q R H H1.
split.
Search "/\".
apply proj1 in H. assumption.
apply proj2 in H1. assumption.
Defined.

Module Or.
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.
End Or.

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
fun (P Q: Prop) (H: P \/ Q) =>
match H with
| or_introl P => or_intror P
| or_intror Q => or_introl Q
end.


Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

End Ex.


Definition some_nat_is_even : exists n, even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

Definition ex_ev_Sn : ex (fun n => even (S n)) :=
ex_intro (fun n => even (S n)) 1 (ev_SS 0 ev_0).


Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .

End Props.

(* Equality *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.
Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X -> Prop, P x -> P y.
Proof.
intros.
inversion H.
rewrite <- H2.
assumption.
Qed.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P:X -> Prop, P x -> P y) -> x == y.
Proof.
intros.
apply H.
apply eq_refl.
Qed.

