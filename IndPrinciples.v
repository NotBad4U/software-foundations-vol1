Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *) simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity. Qed.


Check nat_ind.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
induction n.
- reflexivity.
- simpl. rewrite IHn. reflexivity.
Qed.

Inductive yesno : Type :=
  | yes
  | no.

Check yesno_ind.

Inductive rgb : Type :=
  | red
  | green
  | blue.

(**
rgb_ind
     : forall P : rgb -> Prop, P red -> P green -> P blue -> forall y : rgb, P y
*)
Check rgb_ind.

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

(**
natlist_ind
     : forall P : natlist -> Prop, P nnil -> (forall (n:nat) (l:listnat): P l -> P (ncons n l))) -> forall y : natlist, P y
*)
Check natlist_ind.

Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l : natlist1) (n : nat).

Check natlist1_ind.

Inductive byntree : Type :=
 | bempty
 | bleaf (yn : yesno)
 | nbranch (yn : yesno) (t1 t2 : byntree).


(**
byntree_ind
     : forall P : byntree -> Prop, P bempty -> (forall (yn: yesno): P yn -> P rgb_ind yn) ->
      (forall (yn: yesno): (forall (t1 t2 :byntree): P yn t1 t2 -> P nbranch yn t1 t2 )) -> 
      forall y : byntree_ind, P y
*)

Check byntree_ind.

(**
  byntree_ind
     : forall P : byntree -> Prop,
       P bempty ->
       (forall yn : yesno, P (bleaf yn)) ->
       (forall (yn : yesno) (t1 : byntree), P t1 -> forall t2 : byntree, P t2 -> P (nbranch yn t1 t2)) ->
       forall b : byntree, P b
*)


(** Find an inductive definition that gives rise to the following induction principle:
 ExSet_ind :
         ∀P : ExSet → Prop,
             (∀b : bool, P (con1 b)) →
             (∀(n : nat) (e : ExSet), P e → P (con2 n e)) →
             ∀e : ExSet, P e
*)
Inductive ExSet : Type :=
| cons1 (b :bool)
| cons2 (n:nat) (e: ExSet)
.

Check ExSet_ind.

(* Polymorphism *)

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Check list_ind.

Inductive tree (X:Type) : Type :=
| leaf (x : X)
| node (t1 t2 : tree X).

(**
tree_ind:
  : forall (X: Type) (P: tree X -> Prop),
  forall x: X, P (leaf x X) ->
  (forall (t1: tree X): P t1 -> forall t2: tree X, P t2 -> P (node X t1 t2)) -> forall t: tree, P t.
*)

Check tree_ind.

(**
tree_ind
     : forall (X : Type) (P : tree X -> Prop),
       (forall x : X, P (leaf X x)) ->
       (forall t1 : tree X, P t1 -> forall t2 : tree X, P t2 -> P (node X t1 t2)) ->
       forall t : tree X, P t
*)


(** Find an inductive definition that gives rise to the following induction principle:
  mytype_ind :
        ∀(X : Type) (P : mytype X → Prop),
            (∀x : X, P (constr1 X x)) →
            (∀n : nat, P (constr2 X n)) →
            (∀m : mytype X, P m →
               ∀n : nat, P (constr3 X m n)) →
            ∀m : mytype X, P m
*)

Inductive mytype (X: Type): Type :=
| constr1 (x: X)
| constr2 (n:nat)
| constr3 (m: mytype X) (n :nat)
.

Check mytype_ind.


(** Find an inductive definition that gives rise to the following induction principle:
∀(X Y : Type) (P : foo X Y → Prop),
     (∀x : X, P (bar X Y x)) →
     (∀y : Y, P (baz X Y y)) →
     (∀f1 : nat → foo X Y,
       (∀n : nat, P (f1 n)) → P (quux X Y f1)) →
     ∀f2 : foo X Y, P f2
*)
Inductive foo ( X Y : Type ) : Type :=
| bar : X ->  foo X Y
| baz : Y -> foo X Y
| quxx : ( nat -> foo X Y ) -> foo X Y.

Check foo_ind.




(* Induction Hypotheses *)

Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind.
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* Note the proof state at this point! *)
    (*  ∀ n', P_m0r n' → P_m0r (S n') *)
    intros n IHn.
    unfold P_m0r in IHn. unfold P_m0r. simpl. apply IHn. Qed.


(* More on the induction Tactic *)

Theorem plus_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary n, m, and
     p..." *)
  intros n m p.
  (* ...We now use the induction tactic to prove P n (that
     is, n + (m + p) = (n + m) + p) for _all_ n,
     and hence also for the particular n that is in the context
     at the moment. *)
  induction n as [| n'].
  - (* n = O *) reflexivity.
  - (* n = S n' *)
    (* In the second subgoal generated by induction -- the
       "inductive step" -- we must prove that P n' implies
       P (S n') for all n'.  The induction tactic
       automatically introduces n' and P n' into the context
       for us, leaving just P (S n') as the goal. *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_comm' : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. reflexivity.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. reflexivity. Qed.

Theorem plus_comm'' : forall n m : nat,
  n + m = m + n.
Proof.
  (* Let's do induction on m this time, instead of n... *)
  induction m as [| m'].
  - (* m = O *) simpl. rewrite <- plus_n_O. reflexivity.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. reflexivity. Qed.










