Set Warnings "-notation-overridden,-parsing".

From LF Require Export Tactics.
Require Import Setoid.


Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.

(* Logical Connectives *)


Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.


Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
intros n m H.
split.
destruct n.
reflexivity.
discriminate.
destruct m.
reflexivity.
rewrite <- plus_n_Sm in H.
discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn; rewrite Hm; reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
intros P Q H.
destruct H as [HP HQ].
apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(* "from falsehood follows whatever you like" *)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Lemma my_neg_false: forall (A : Prop), ~ A <-> (A <-> False).
Admitted.

(* test *)
Fact not_implies_our_not : forall (P:Prop),
  not P -> (forall (Q:Prop), P -> Q).
Proof.
intros P H Q.
rewrite my_neg_false in H.
destruct H.
intro.
destruct H.
apply H1.
Qed.

(* tru answer *)
Fact not_implies_our_not' : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HNP Q HP.
  destruct HNP.
  apply HP.
Qed.

Theorem zero_not_one : (~(0 = 1)).
Proof.
unfold not.
intros contra.
discriminate.
Qed.

Theorem not_False :
  ~False.
Proof.
  unfold not. intros H. destruct H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP. Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
intros P HP.
unfold not.
intros HNP.
apply HNP in HP.
destruct HP.
Qed.

Theorem double_neg' : forall P : Prop,
  P -> ~~P.
Proof.
intros P H.
unfold not.
intros G.
apply G.
apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
intros P Q H.
unfold not.
intros HNQ HP.
apply H in HP.
apply HNQ in HP.
destruct HP.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
intros P.
unfold not.
intros H.
destruct H.
apply H0 in H.
destruct H.
Qed.

Theorem not_true_is_false : forall b : bool,
  (~(b = true)) -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  (~(b = true)) -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros P Q R.
unfold iff.
split.
- intro H. inversion H.
  + split. left. apply H0. left. apply H0.
  + split.
    * apply proj1 in H0. right. apply H0.
    * apply proj2 in H0. right. apply H0.
 -  intro H.
    inversion H as [[H1P | H1Q] [H2P | H2R]].
    + left. apply H1P.
    + left. apply H1P.
    + left. apply H2P.
    + right. split. apply H1Q. apply H2R.
Qed.


Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
Admitted.


Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc. reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. assumption.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~P x).
Proof.
intros.
unfold not.
intro.
destruct H0 as [x E].
destruct E.
apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
intros X P Q.
split.
- intros. destruct H as [x H]. destruct H as [ HP | HQ ].
  + left. exists x. apply HP.
  + right. exists x. apply HQ.
- intros H. destruct H as [E1 | E2 ].
  + destruct E1 as [x H]. exists x. left. apply H.
  + destruct E2 as [x H]. exists x. right. apply H.
Qed.


(* Programming with Propositions *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
simpl. right. right. right. left. reflexivity.
Qed.

Require Import Coq.Classes.RelationClasses.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - intros H. induction l as [| x' l' IHl'].
    +  (* l = [] *) simpl in H. destruct H.
    +  (* l = x' :: l' *) simpl in H. destruct H as [H1 | H2].
      *  exists x'. split.
         { apply H1. }
         { simpl. left. reflexivity. }
      *  apply IHl' in H2. destruct H2 as [x2 H2]. exists x2. split.
          { apply proj1 in H2. assumption. }
          { simpl. right. apply proj2 in H2. assumption. }
  - intro H. induction l as [| x' l' IHl'].
    + (* l = [] *) simpl. destruct H. simpl in H. apply proj2 in H. assumption.
    +  (* l = x' :: l' *) simpl. simpl in H. destruct H as [x'' H]. inversion H.  destruct H1 as [H2 | H3].
      { left. rewrite H2. assumption. }
      { right.  apply IHl'. exists x''. split.
        - apply H0.
        - apply H3.
      }
Qed.


Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
intros A l l' x. split.
- intro H. induction l as [| x' l'' IHl''].
  + (* l = [] *) simpl in H. right. assumption.
  + (* l = x' :: l' *) simpl in H. destruct H as [H1 | H2].
    * rewrite H1. simpl. left. left. reflexivity.
    * apply IHl'' in H2. simpl. apply or_assoc. right. assumption.
- intro H. induction l as [| x' l'' IHl''].
  + (* l = [] *) simpl in H. destruct H.
    * exfalso. assumption.
    * simpl. assumption.
  + (* l = x' :: l' *) simpl in H. simpl. destruct H.
    *  destruct H. 
        { left. apply H. }
        { right. apply IHl''. left. assumption.  }
    * right. apply IHl''. right. assumption.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
intros T P l.
split.
- intros H. induction l as [| x' l' IHl'].
  +  simpl. reflexivity.
  + simpl. split.
    *  apply H. simpl. left. reflexivity.
    *  apply IHl'. intros x HIN.  apply H. simpl. right. assumption.
- intros H. induction l as [| x' l' IHl'].
  +  intros x H'. simpl in H'. destruct H'.
  + simpl. intros x H'. destruct H'.
     { simpl in H. apply proj1 in H. rewrite <- H0.   apply H.  }
     { apply IHl'. simpl in H. apply H. apply H0. }
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
fun n => if oddb n then Podd n else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
intros Podd Peven n H H1.
unfold combine_odd_even.
destruct (oddb n).
- apply H. reflexivity.
- apply H1. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
intros Podd Peven n H H1.
unfold combine_odd_even in H.
rewrite H1 in H.
apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
intros Podd Peven n H H1.
unfold combine_odd_even in H.
rewrite H1 in H.
apply H.
Qed.

(* Applying Theorems to Arguments *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm HT]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(* Coq vs. Set Theory *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
intros X. apply functional_extensionality. intros l.
induction l as [|x l' IHl' ].
- reflexivity.
- simpl. rewrite <- IHl'. unfold tr_rev. simpl.
Admitted.


(*  Hint: Use the [evenb_S] lemma from [Induction.v]. *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
intros n. induction n as [| n'].
- simpl. exists 0. reflexivity.
- destruct (evenb n') eqn: Heq.
  + rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
    exists n''. rewrite IHn'. reflexivity.
    + rewrite evenb_S. rewrite Heq. simpl. destruct IHn' as [n'' IHn'].
      (* boring chain of rewrite, use exists n''+1 ... *)
  Admitted.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. simpl.  split. 
    + rewrite andb_commutative in H. apply andb_true_elim2 in H. assumption.
    + apply andb_true_elim2 in H. assumption.
  - intros H. inversion H. rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. split.
  - intros H. destruct b1.
    + left. reflexivity.
    + right. apply H.
  - intro H. destruct H.
    + rewrite H. simpl. reflexivity.
    + destruct b1.
      * simpl. reflexivity.
      * simpl. assumption.
Qed.

Theorem eqb_refl: forall n: nat,
  true = (n =? n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Theorem eqb_neq : forall x y : nat,
  x =? y = false <-> (~(x = y)).
Proof.
  split.
  - intros H.
    unfold not.
    intros H1.
    rewrite H1 in H.
    rewrite <- eqb_refl in H.
    discriminate.
  - intro H.
    unfold not in H.
    destruct (x=?y) eqn: E.
    + apply eqb_eq in E.
      apply H in E.
      destruct E.
    + reflexivity.
Qed.

Fixpoint eqb_list {A: Type} (eqb: A->A->bool) (l1 l2: list A): bool :=
  match l1, l2 with
  | [], [] => true
  | h1::t1, h2::t2 => if eqb h1 h2 then eqb_list eqb t1 t2 else false
  | _, _ => false
  end.

Lemma eqb_list_true_iff:
  forall A (eqb: A->A->bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1=a2) ->
      (forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2).
Proof.
  intros A eqb H.
  induction l1 as [|h t iH1].
  - intro l2. destruct l2.
    + simpl. split.
      * reflexivity.
      * reflexivity.
    + split.
      * intro H'. simpl in H'. discriminate.
      * intro H'. simpl in H'. discriminate.
  - destruct l2.
    + split.
      *  intro H'. simpl in H'. discriminate.
      * intro H'. discriminate H'.
    +  split.
       * simpl. intro H'. destruct (eqb h a) eqn: E in H'.
        { apply iH1 in H'. rewrite H'. f_equal. apply H. apply E. }
        { discriminate H'. }
      * simpl. intros H'. injection H' as H1 H2.
        apply H in H1.  rewrite H1.  apply iH1. apply H2.
Qed.

Fixpoint forallb {X: Type} (test: X->bool) (l: list X): bool :=
  match l with
  | [] => true
  | h::t => andb (test h) (forallb test t)
  end.



Theorem forallb_true_iff: forall X test (l: list X),
  forallb test l = true <-> All (fun x => test x = true) l.
Proof.
intros X test l.
split.
- induction l as [|x l' IHl'].
   + intro H.
      simpl in H.
      simpl.
      reflexivity.
   + intros H.
      simpl.
      simpl in H.
      split.
       * rewrite andb_commutative in H. 
          apply andb_true_elim3 in H.
          apply H.
       * apply IHl'.
          apply andb_true_elim3 in H.
          assumption.
- induction l as [|x l' IHl'].
  +  intro H.
      simpl.
      reflexivity.
   + intro H.
      simpl.
      simpl in H.
      inversion H.
      rewrite andb_true_iff.
      split.
        * assumption.
        * apply IHl'. apply H1.
Qed.


Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** should be in Tactic.v and Logic.v *)

Theorem beq_nat_true : forall n m,
    eqb n m = true -> n = m.
Proof.
  intros n. induction n as [| n'].
  - simpl. intros m . destruct m as [| m']. 
    + reflexivity.
    + intro contra. inversion contra.

  - intros m. simpl. induction m.
    + intros H. inversion H.
    + intros H. apply IHn' in H. rewrite H. reflexivity.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  eqb n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- eqb_nat_refl. reflexivity.
Qed.

(** *****************************  *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (eqb n m)).
  symmetry.
  Search "nat_true_iff".
  apply beq_nat_true_iff.
Qed.


Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~~(P \/ ~P).
Proof.
intros P.
unfold not.
intros.
apply H.
right.
intros.
apply H.
left.
assumption.
Qed.



(** For those who like a challenge, here is an exercise taken from the
    Coq'Art book by Bertot and Casteran (p. 123).  Each of the
    following four statements, together with [excluded_middle], can be
    considered as characterizing classical logic.  We can't prove any
    of them in Coq, but we can consistently add any one of them as an
    axiom if we wish to work in classical logic.
    Prove that all five propositions (these four plus
    [excluded_middle]) are equivalent. *)

Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(* FILL IN HERE *)
