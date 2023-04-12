From Coq Require Export String.

(** ** BOOLEANS *)
Inductive bool : Type :=
    | true
    | false.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(** Exercise 1 *)
Definition nandb (b1 : bool) (b2 : bool) : bool :=
    match b1 with
    | true => negb b2
    | false => true
    end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(** Exercise 2 *)
Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
    b1 && b2 && b3.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

Inductive rgb : Type :=
    | red
    | green
    | blue.

Inductive color : Type :=
    | black
    | white
    | primary (p: rgb).

Definition monochrome (c : color) : bool :=
    match c with
    | black => true
    | white => true
    | primary p => false
    end.

Definition isred (c : color) : bool :=
    match c with
    | primary red => true
    | _ => false
    end.


(** TUPLES *)
Module TuplePlayground.
    Inductive bit : Type :=
        | B0
        | B1.

    Inductive nybble : Type :=
        | bits (b0 b1 b2 b3 : bit).

    Check (bits B1 B0 B0 B1) : nybble.

    Definition all_zero (nybble : nybble) : bool :=
        match nybble with
        | bits B0 B0 B0 B0 => true
        | _ => false
        end.

    Example all_zero_test1: (all_zero (bits B0 B0 B0 B0)) = true.
    Proof. simpl. reflexivity. Qed.
    Example all_zero_test2: (all_zero (bits B0 B0 B1 B1)) = false.
    Proof. simpl. reflexivity. Qed.
End TuplePlayground.

Module NatPlayground.
    Inductive nat : Type :=
        | O
        | S (n : nat).

    Definition pred (n : nat) : nat :=
        match n with
        | O => O
        | S n => n
        end.

    Example pred_of_one: O = pred (S O).
    Proof. simpl. reflexivity. Qed.
    Example pred_of_two: (S O) = pred (S (S O)).
    Proof. simpl. reflexivity. Qed. 
End NatPlayground.

Check (S (S (S O))).
Check (S 2).

Fixpoint even (n : nat) : bool :=
    match n with
    | O => true
    | S O => false
    | S (S m) => even m
    end.

Definition odd (n : nat) : bool :=
    negb (even n).

Example test_odd1 : odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2 : odd 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
    Fixpoint plus (n : nat) (m : nat) : nat :=
        match n with
        | O => m
        | S (n') => S (plus n' m)
        end.

    Example test_plus1 : (plus 3 2) = 5.
    Proof. simpl. reflexivity. Qed.
    Example test_plus2 : (plus 0 10) = 10.
    Proof. simpl. reflexivity. Qed.

    Fixpoint mult (n m : nat) : nat :=
        match n with
        | O => O
        | S n' => plus m (mult n' m)
        end.

    Example test_mult1 : (mult 4 3) = 12.
    Proof. simpl. reflexivity. Qed.
    Example test_mult2 : (mult 2 0) = 0.
    Proof. simpl. reflexivity. Qed.
End NatPlayground2.

(** Exercise 3 *)
Fixpoint factorial (n : nat) : nat :=
    match n with
    | 0 => 1
    | S n1 => n * (factorial n1)
    end.

Example test_factorial1 : 6 = factorial 3.
Proof. simpl. reflexivity. Qed.
Example test_factorial2 : 1 = factorial 1.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
    match n, m with
    | O, O => true
    | O, _ => false
    | _, O => false
    | S n1, S m1 => eqb n1 m1
    end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Example test_eqb1 : eqb 5 5 = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb2 : eqb 1 2 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb3 : eqb 2 1 = false.
Proof. simpl. reflexivity. Qed.
Example test_eqb3' : (2 =? 1) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint leb (n m : nat) : bool :=
    match n, m with
    | O, _ => true
    | S n1, O => false
    | S n1, S m1 => leb n1 m1
    end.

Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.
Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool := 
    negb (n =? m) && negb (leb m n).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_ltb3': (4 <? 2) = false.
Proof. simpl. reflexivity. Qed.
