From LF Require Export Induction.
From LF Require Export Basics.


Module NatList.


(* ## Pairs of Numbers *)

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Definition fst (p : natprod) : nat :=
match p with
| pair x y => x
end.

Definition snd (p : natprod) : nat :=
match p with
| pair x y => y
end.

Definition swap_pair (p : natprod) : natprod :=
match p with
| pair x y => pair y x
end.

Notation "( x , y )" := (pair x y).


Fixpoint minus (n m : nat) : nat :=
 match n, m with
 | O   , _    => O
 | S _ , O    => n
 | S n', S m' => minus n' m'
 end.


Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [x y].
  simpl.
  reflexivity.
Qed.


Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [x y].
  simpl.
  reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [x y].
  simpl.
  reflexivity.
Qed.

(* # Lists of Numbers *)

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
match count with
| O => nil
| S count' => n :: (repeat n count')
end.

Fixpoint length (l:natlist) : nat :=
match l with
| nil => O
| h :: t => S (length t)
end.

Fixpoint app (l1 l2 : natlist) : natlist :=
match l1 with
| nil => l2
| h :: t => h :: (app t l2)
end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition hd (default:nat) (l:natlist) : nat :=
match l with
| nil => default
| h :: t => h
end.

Definition tl (l:natlist) : natlist :=
match l with
| nil => nil
| h :: t => t
end.

Fixpoint nonzeros (l:natlist) : natlist :=
match l with
| nil => nil
| cons O t => (nonzeros t)
| cons x t => x :: (nonzeros t)
end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  simpl. reflexivity.
Qed.


Fixpoint oddmembers (l:natlist) : natlist :=
match l with
| nil => nil
| h :: t => if(oddb h) then h :: oddmembers t else oddmembers t
end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  simpl.
  reflexivity.
Qed.

Definition countoddmembers (l:natlist) : nat := length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  simpl.
  reflexivity.
Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  simpl.
  reflexivity.
Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  simpl.
  reflexivity.
Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1, l2 with
| nil, nil => nil
| nil, _ => l2
| _, nil => l1
| h :: t, h' :: t' => h :: h' :: (alternate t t')
end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
reflexivity.
Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
reflexivity.
Qed.

Definition bag := natlist.

Fixpoint filter (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| h :: t => if eqb h v then h :: filter v t else filter v t
end.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => if(eqb h v) then 1 + (count v t) else count v t 
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
 reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
  reflexivity.
Qed.

Definition sum : bag -> bag -> bag :=
  fun l1 l2 => l1 ++ l2.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
 simpl. reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag :=
  (v :: nil) ++ s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  reflexivity.
Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  simpl. reflexivity.
Qed.

Definition member (v:nat) (s:bag) : bool :=
match (count v s) with
| O => false
| S n => true
end.

Example test_member1: member 1 [1;4;1] = true.
reflexivity.
Qed.

Example test_member2: member 2 [1;4;1] = false.
reflexivity.
Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| h :: t => if(eqb v h) then t else h :: remove_one v t
end.


Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.


Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| h :: t => if(eqb v h) then remove_all v t else h :: remove_all v t
end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint exist (v:nat) (s:bag) : bool :=
  match s with
  | nil => false
  | h :: t => if (eqb v h) then true else exist v t
end.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => if exist h s2 then subset t (remove_one h s2) else false
end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* # Reasoning About Lists *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l.
  destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
  reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
match l with
| nil => nil
| h :: t => rev t ++ [h]
end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
intros l1 l2.
induction l1 as [| n l1' IHl1'].
- (* l1 = nil *)
  reflexivity.
- (* l1 = cons *)
  simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> app_length, plus_comm.
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
intros l.
induction l as [| n l' IHl'].
- simpl. reflexivity.
- simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. apply app_assoc.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [| n l' IHl].
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr.
    rewrite -> IHl.
    reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros l1 l2 l3 l4.
rewrite -> app_assoc.
rewrite -> app_assoc.
reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros l1 l2. induction l1 as [| n1 l1'].

- reflexivity.
- simpl.
  rewrite -> IHl1'.
  destruct n1 as [| n1'].
  + reflexivity.
  + reflexivity.
Qed.


Fixpoint eqblist (l1 l2 : natlist) : bool :=
match l1, l2 with
| nil, nil => true
| nil, _ => false
| _, nil => false
| h :: t, h' :: t' => if eqb h h' then eqblist t t' else false
end.

Example test_beq_natlist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_beq_natlist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_beq_natlist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l as [| n l'].
  - reflexivity.
  - { induction n.
    - simpl. rewrite <- IHl'. reflexivity.
    - rewrite -> IHn. simpl. reflexivity. }
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
intros s. reflexivity.
Qed.


Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
    simpl. reflexivity.
    simpl. rewrite IHn'. reflexivity.
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s.
  - simpl. reflexivity.
  - simpl. { induction n.
             - simpl. rewrite leb_n_Sn. reflexivity.
             - simpl. rewrite IHs. reflexivity. 
           }
Qed.


(* Options *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
match l with
| nil => 42 (* arbitrary! *)
| a :: l' => match n =? O with
             | true => a
             | false => nth_bad l' (pred n)
             end
end.

Inductive natoption : Type :=
| Some (n : nat)
| None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
match l with
| nil => None
| a :: l' => if n =? O then Some a
             else nth_error l' (pred n)
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
simpl. reflexivity.
Qed.

Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
simpl. reflexivity.
Qed.

Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
simpl. reflexivity.
Qed.

Definition option_elim (d : nat) (o : natoption) : nat :=
match o with
| Some n' => n'
| None => d
end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | a :: l => Some a
end.

Example test_hd_error1 : hd_error [] = None.
reflexivity.
Qed.

Example test_hd_error2 : hd_error [1] = Some 1.
reflexivity.
Qed.

Example test_hd_error3 : hd_error [5;6] = Some 5.
reflexivity.
Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
 intros l def. induction l as [| n l' IHl].
  - reflexivity.
  - reflexivity.
Qed.





(* Partial Maps *)

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
match x1, x2 with
| Id n1, Id n2 => n1 =? n2
end.

Theorem eqb_id_refl : forall x, true = eqb_id x x.
Proof.
intros x.
destruct x.
simpl.
Search "nat_refl".
apply eqb_nat_refl.
Qed.

Module PartialMap.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.


Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros d k v.
  simpl.
  rewrite <- eqb_id_refl.
  reflexivity.
Qed.

Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    eqb_id x y = false -> find x (update d y o) = find x d.
Proof.
  intros d k v o H.
  simpl.
  rewrite H.
  reflexivity.
Qed.


End PartialMap.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

End NatList.