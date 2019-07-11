(*File containing lists and poly examples*)

(** Before getting started, we need to import all of our
    definitions from the previous chapter: *)

From LF Require Export Basics.
Module MyLists.

Inductive natprod : Type :=
| pair (n1 n2 : nat). 

Notation "( x , y )" := (pair x y).

Definition minus'' (p: natprod) : nat :=
  match p with
  | (x, y) => x-y
  end.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(*Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h::t => match (h =? v) with
                | true => 1+(count v t)
                | false => (count v t)
                end
  end. 
*)

Inductive id : Type :=
  | Id (n : nat).

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
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
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

(*Examples for reasoning about lists*)
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(*Example 1: simpl*)
Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. simpl. reflexivity. Qed.

(*Example 2: destruct*)
Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    simpl. reflexivity.
  - (* l = cons n l' *)
    simpl. reflexivity.  Qed.

(*Example 3: induction*)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    simpl. reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

End MyLists.
(**********************Polymorphism******************************)

Module MyPoly.
Export MyLists.

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(*Check list.
(* ===> list : Type -> Type *)*)

Check nil.

(*Type Annotation Inference*)
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

(*Type Argument Inference*)
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(*Implict Arguments*)
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Check nil.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** Now lists can be written just the way we'd hope: *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Definition list123''' := [1; 2; 3].

(*Polymorphism Pairs*)
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

(*Note: Module MyPoly is need, as constructor [pair] has used in natprod*)

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Fail Definition mynil : list := nil.

Check nil.

Definition mynil : list nat := nil.
Check mynil.
Definition mynil' := @nil nat.
Check mynil'.

(*Polymorphic Options*)
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l  with
  | nil => None
  | a::l' => Some a
  end.

(*High-order functions*)
Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity.  Qed.

(*Anonymous Functions*)
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity.  Qed.

(*Functions That Construct Functions*)
Definition constfun {X: Type} x : nat->X :=
  fun (k:nat) => x.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.


(*************************Example: Map*****************************)

(*Input f, l=[n1,n2......]   output: [f n1, f n2, ......]*)
Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. simpl. reflexivity.  Qed.

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

(**)
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).
(**)


(**)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f.
  induction l as [| h t Ht].
  - (* l = [] *)
    simpl. reflexivity.
  - (* l = h t *)
    simpl. rewrite <- Ht. simpl. reflexivity.
Qed.
(**)

Theorem map_app_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h1 t1 IHt1].
  - (* l1 = [] *)
    simpl. reflexivity.
  - (* l1 = h1 t1 *)
    simpl. rewrite -> IHt1. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f.
  induction l as [| h t Ht].
  - (* l = [] *)
    simpl. reflexivity.
  - (* l = h t *)
    simpl.  rewrite <- Ht. rewrite -> map_app_distr. simpl. reflexivity.
Qed.

End MyPoly.