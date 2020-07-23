Set Warnings "-notation-overridden,-parsing".

From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.
Module MumbleGrumble.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

End MumbleGrumble.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.


Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.


Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).


Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.


Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Fixpoint repeat {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat x count')
  end.


Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


Definition list123''' := [1; 2; 3].


Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
intros X l.
induction l as [| n l' IHl'].
- simpl. reflexivity.
- simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
Proof.
intros X l1 l2.
induction l1 as [| n l1' IHl1'].
- (* l1 = nil *)
  reflexivity.
- (* l1 = cons *)
  simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1.
  - simpl. rewrite  -> app_nil_r. reflexivity.
  - simpl.
  rewrite -> IHl1.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l.
  - simpl. reflexivity.
  - simpl.
  rewrite -> rev_app_distr.
  rewrite -> IHl.
  simpl.
  reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

(** As with lists, we make the type arguments implicit and define the
    familiar concrete notation. *)

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t => (x :: (fst (split t)), y :: (snd (split t)))
  end.

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
reflexivity.
Qed.


Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
match l with
| [] => None
| a :: l' => if n =? O then Some a else nth_error l' (pred n)
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
reflexivity.
Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
reflexivity.
Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
reflexivity.
Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
match l with
| nil => None
| a :: l => Some a
end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
reflexivity.
Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
reflexivity.
Qed.

Fixpoint filter {X:Type} (test: X -> bool) (l:list X)
                : (list X) :=
match l with
| [] => []
| h :: t => if test h then h :: (filter test t) else filter test t
end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.


Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.



Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (negb (leb n 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. simpl. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. simpl. reflexivity. Qed.


(*
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : (prod (list X) (list X))
pair (filter test l) (filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity.  Qed.

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity.  Qed.

*)

Fixpoint map {X Y: Type} (f:X -> Y) (l:list X) : (list Y) :=
match l with
| [] => []
| h :: t => (f h) :: (map f t)
end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

Theorem map_assoc : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
    map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2.
  induction l1.
  - reflexivity.
  - simpl. rewrite -> IHl1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
intros X Y f l.
induction l as [| x l' IHl].
- reflexivity.
- simpl.
  rewrite -> map_assoc.
  rewrite <- IHl.
  reflexivity.
Qed.

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X) : (list Y) :=
match l with
| nil => nil
| h :: t => f h ++ (flat_map f t)
end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
match xo with
  | None => None
  | Some x => Some (f x)
end.


Fixpoint fold {X Y: Type} (f: X -> Y ->Y) (l: list X) (b: Y) : Y :=
match l with
| nil => b
| h :: t => f h (fold f t b)
end.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.


Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.


(* Additional Exercises *)
Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
reflexivity.
Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
intros X l.
induction l as [|h l' IHl].
- reflexivity.
- simpl. rewrite <- IHl. reflexivity.
Qed.

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
fold (fun x acc => f x :: acc) l [].


Theorem fold_map_correct : forall X Y (l : list X) (f: X -> Y),
  fold_map f l = map f l.
Proof.
intros X Y l f.
induction l as [| h l' IHl].
- reflexivity.
- simpl. rewrite <- IHl. reflexivity.
Qed.

End Exercises.