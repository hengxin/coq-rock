





Theorem plus_0_n : forall n:nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity.  Qed.

Theorem mult_0_plus : forall n m:nat, (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity.
  Qed.






Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

Theorem plus_1_l : forall n:nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.  Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [ | n' IHn'].
  + simpl. reflexivity. 
  + simpl. rewrite -> IHn'. reflexivity.
  Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [ | n' IHn'].
  + simpl. rewrite <- plus_n_O. reflexivity.
  + simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
  Qed.

Lemma plus_1_r : forall n : nat,
  S n = n + 1.
Proof.
  intros n.
  rewrite -> plus_comm.
  rewrite <- plus_1_l.
  reflexivity.
  Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [ | n' IHn'].
  + simpl. reflexivity. 
  + simpl. rewrite -> IHn'. reflexivity.
  Qed.


Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert (H1: m + n = n + m).
  + rewrite -> plus_comm. reflexivity.
  + rewrite -> H1. reflexivity.
  Qed. 

(** **** 

        coq defination of binary numbers.


        decimal            binary                           unary
           0                   Z                              O
           1                 B Z                            S O
           2              A (B Z)                        S (S O)
           3              B (B Z)                     S (S (S O))
           4           A (A (B Z))                 S (S (S (S O)))
           5           B (A (B Z))              S (S (S (S (S O))))
           6           A (B (B Z))           S (S (S (S (S (S O)))))
           7           B (B (B Z))        S (S (S (S (S (S (S O))))))
           8        A (A (A (B Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate. *)

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).


(* increment function for binary numbers                 *)
Fixpoint incr (m:bin) : bin :=
  match m with
  |Z => B Z
  |A n => B n
  |B n => A (incr (n))
  end.

(* convert binary numbers to unary numbers                *)
Fixpoint bin_to_nat (m:bin) : nat :=
  match m with 
  |Z => 0
  |A n => 2 * bin_to_nat(n)
  |B n => 2 * bin_to_nat(n) + 1
  end.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b as [ |b1 | b2]. 
  + simpl. reflexivity.
  + simpl. rewrite <- plus_n_O. rewrite <- plus_1_r.  reflexivity.
  + simpl. rewrite <- plus_n_O. rewrite <- plus_n_O.  rewrite -> IHb2.
    simpl.
  replace (S (bin_to_nat b2)) with (bin_to_nat b2 + 1).
    - rewrite -> plus_assoc. reflexivity.
    - rewrite <- plus_1_r. reflexivity.
  Qed.
  



(*  this is an exercise of chapter 2                            *)


(*
(a) First, write a function to convert natural numbers to binary
        numbers. *)

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with 
  |0 => Z
  |S n => incr (nat_to_bin n)
  end.

(** Prove that, if we start with any [nat], convert it to binary, and
    convert it back, we get the same [nat] we started with. *) 

Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [ | n' IHn'].
  + simpl. reflexivity.
  + simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity.
  Qed.


(** (b) One might naturally expect that we should also prove the
        opposite direction -- that starting with a binary number,
        converting to a natural, and then back to binary should yield
        the same number we started with.  However, this is not the
        case!  Explain (in a comment) what the problem is. *)


(** (c) Define a normalization function -- i.e., a function
        [normalize] going directly from [bin] to [bin] (i.e., _not_ by
        converting to [nat] and back) such that, for any binary number
        [b], converting [b] to a natural and then back to binary yields
        [(normalize b)].  Prove it.   *)

Fixpoint norbin_trans (n : nat) : bin :=
  match n with
  |0 => Z
  |S n' => A (nat_to_bin (n) )
  end.

Fixpoint norbin (b : bin) : bin :=
  match b with
  |Z => Z
  |B n => B (norbin n)
  |A n => norbin_trans (bin_to_nat n)
  end.



Lemma nat_to_bin_double : forall n : nat, nat_to_bin (n + n) =
 norbin (A (nat_to_bin n)).
Proof.  Admitted.

Theorem norbin_equal : forall b : bin, bin_to_nat (norbin b) = bin_to_nat b.
Proof.  Admitted.

Lemma nat_to_bin_double_plus_1 : forall n : nat, nat_to_bin (n + n + 1) =
  (B (nat_to_bin n)).
Proof.  Admitted.

Theorem bin_nat_bin : forall b : bin, nat_to_bin (bin_to_nat b) = norbin b.
 Proof.
  intros b. induction b as [ |b1 IHb1 |b2 IHb2].
  + simpl. reflexivity.
  + simpl. rewrite <- plus_n_O. rewrite -> nat_to_bin_double. rewrite -> IHb1.
    simpl. rewrite -> norbin_equal. reflexivity.
  + simpl. rewrite <- plus_n_O. rewrite -> nat_to_bin_double_plus_1. rewrite -> IHb2.
    reflexivity.
Qed.


Lemma nat_to_bin_double' : forall n : nat, nat_to_bin (n + n) =
 norbin (A (nat_to_bin n)).
Proof. 
  intros n. induction n as [ |n' IHn'].
  + simpl. reflexivity.
  + simpl.  rewrite -> bin_to_nat_pres_incr. rewrite -> nat_bin_nat. simpl.
    assert(H : n' + S n' = S (n' + n')).
    - rewrite -> plus_comm. simpl. reflexivity.
    - rewrite -> H. simpl.  rewrite -> IHn'.  simpl. rewrite -> nat_bin_nat.
      destruct n' as [ |n''].
      * simpl. reflexivity.
      * simpl. reflexivity.
Qed.
 

Theorem norbin_equal' : forall b : bin, bin_to_nat (norbin b) = bin_to_nat b.
Proof.
  induction b as [ |b' IHb' |b' IHb'].
  + simpl. reflexivity.
  + simpl. rewrite <- plus_n_O. destruct (bin_to_nat b') as [ |n'].
    - simpl. reflexivity.
    - simpl. rewrite <- plus_n_O. rewrite -> bin_to_nat_pres_incr. rewrite -> nat_bin_nat.
     reflexivity.
  + simpl. rewrite <- plus_n_O. rewrite <- plus_n_O. rewrite -> IHb'. reflexivity.
Qed.

Lemma nat_to_bin_double_plus_1' : forall n : nat, nat_to_bin (n + n + 1) =
  (B (nat_to_bin n)).
Proof.
  intros n. induction n as [ |n' IHn'].
   + simpl. reflexivity.
   + simpl. rewrite -> plus_comm. rewrite -> plus_assoc. simpl. rewrite -> plus_1_r. 
      rewrite -> plus_assoc. rewrite -> IHn'. simpl. reflexivity.
Qed.  

