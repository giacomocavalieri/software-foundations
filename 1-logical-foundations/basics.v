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

(** PROOF BY SIMPLIFICATION *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m : nat,
    n = m -> n + m = m + n.
Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity.
Qed.

(** Exercise 4 *)
Theorem plus_id_exercise : forall n m o : nat,
    n = m -> 
    m = o ->
    n + m = m + o.
Proof.
    intros n m o.
    intros H1.
    intros H2.
    rewrite H1.
    rewrite H2.
    reflexivity.
Qed.

Theorem mult_n_0_m_0 : forall n m : nat,
    (n * 0) + (m * 0) = 0.
Proof.
    intros p q.
    rewrite <- mult_n_O.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
    p * 1 = p.
Proof.
    intros p.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_O.
    simpl.
    reflexivity.
Qed.

(** Proof by case analysis *)
Theorem plus_1_neq_0_first_try : forall n : nat,
    (n + 1) =? 0 = false.
Proof.
    intros n.
    simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
    (n + 1 =? 0) = false.
Proof.
    intros n. destruct n as [ | n'] eqn:E.
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b. destruct b eqn:B.
        - simpl. reflexivity.
        - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b1 b2 : bool,
    b1 && b2 = b2 && b1.
Proof.
    intros b1 b2.
    destruct b1 eqn:B1.
        - destruct b2 eqn: B2.
            + simpl. reflexivity.
            + simpl. reflexivity.
        - destruct b2 eqn: B2.
            + simpl. reflexivity.
            + simpl. reflexivity.
Qed.

(** Exercise *)
Theorem andb_true_elim2: forall b c : bool,
    b && c = true -> c = true.
Proof.
    intros b c.
    destruct b eqn:B.
        - simpl. intros H. rewrite -> H. reflexivity.
        - simpl. intros H.
          destruct c eqn:C.
            + reflexivity.
            + rewrite H. reflexivity.
Qed.

(** Exercise *)
Theorem zero_nbeq_plus_1 : forall n : nat,
    (0 =? n + 1) = false.
Proof.
    intros [ | m].
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.

(** ** MORE EXERCISES *)

Theorem identity_fn_applied_twice : forall f : bool -> bool,
    (forall x : bool, f x = x) -> (forall b : bool, f (f b) = b).
Proof.
    intros f H b.
    rewrite H. rewrite H.
    reflexivity.
Qed.

Theorem negation_fn_applied_twice : forall f : bool -> bool,
    (forall x : bool, f x = negb x) -> (forall b : bool, f (f b) = b).
Proof.
    intros f H b.
    rewrite H. rewrite H.
    destruct b eqn:B.
        - reflexivity.
        - reflexivity.
Qed.

Theorem andb_eq_orb : forall b c : bool,
    b && c = b || c -> b = c.
Proof.
    intros b c.
    destruct b eqn:B.
        - simpl. intros H. rewrite H. reflexivity.
        - simpl. intros H. rewrite H. reflexivity.   
Qed.

Module LateDays.
    Inductive letter : Type :=
        | A | B | C | D | F.

    Inductive modifier : Type :=
        | Plus | Natural | Minus.

    Inductive grade : Type :=
        Grade (l : letter) (m : modifier).

    Definition letter_comparison (l1 l2 : letter) : comparison :=
        match l1, l2 with
        | A, A => Eq
        | A, (B | C | D | F) => Gt
        | B, A => Lt
        | B, B => Eq
        | B, (C | D | F) => Gt
        | C, (A | B) => Lt
        | C, C => Eq
        | C, (D | F) => Gt
        | D, (A | B | C) => Lt
        | D, D => Eq
        | D, F => Gt
        | F, (A | B | C | D) => Lt
        | F, F => Eq
        end.

    Theorem letter_comparison_eq : forall l,
        letter_comparison l l = Eq.
    Proof.
        intros l. destruct l eqn:L.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
    Qed.

    Definition modifier_comparison (m1 m2 : modifier) : comparison :=
        match m1, m2 with
        | Plus, Plus => Eq
        | Plus, (Natural | Minus) => Lt
        | Natural, Plus => Lt
        | Natural, Natural => Eq
        | Natural, Minus => Gt
        | Minus, (Plus | Natural) => Lt
        | Minus, Minus => Eq
        end.

    Definition grade_comparison (g1 g2 : grade) : comparison :=
        match g1, g2 with
        | Grade l1 m1, Grade l2 m2 =>
            match (letter_comparison l1 l2) with
            | Eq => modifier_comparison m1 m2
            | Lt => Lt
            | Gt => Gt
            end
        end.

    Example test_grade_comparison1 :
    (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
    Proof. reflexivity. Qed.
    Example test_grade_comparison2 :
    (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
    Proof. reflexivity. Qed.
    Example test_grade_comparison3 :
    (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
    Proof. reflexivity. Qed.
    Example test_grade_comparison4 :
    (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
    Proof. reflexivity. Qed.

    (* Penalty for late submission *)
    Definition lower_letter (l : letter) : letter :=
        match l with
        | A => B 
        | B => C
        | C => D
        | D => F
        | F => F
        end.

    Theorem lower_letter_F_is_F:
        lower_letter F = F.
    Proof.
        simpl. reflexivity.
    Qed.

    Theorem lower_letter_lowers:
        forall l : letter,
        letter_comparison F l = Lt ->
        letter_comparison (lower_letter l) l = Lt.
    Proof.
        intros l H. destruct l eqn:L.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - reflexivity.
        - simpl. rewrite <- H. reflexivity.
    Qed.

    Definition lower_grade (g : grade) : grade :=
        match g with
        | Grade l m =>
            match m with
            | Plus => Grade l Natural
            | Natural => Grade l Minus
            | Minus => 
                match l with
                | F => Grade F Minus
                | _ => Grade (lower_letter l) Plus
                end
            end
        end.

    Example lower_grade_A_Plus : lower_grade (Grade A Plus) = (Grade A Natural).
    Proof. reflexivity. Qed.
    Example lower_grade_A_Natural : lower_grade (Grade A Natural) = (Grade A Minus).
    Proof. reflexivity. Qed.
    Example lower_grade_A_Minus : lower_grade (Grade A Minus) = (Grade B Plus).
    Proof. reflexivity. Qed.
    Example lower_grade_B_Plus : lower_grade (Grade B Plus) = (Grade B Natural).
    Proof. reflexivity. Qed.
    Example lower_grade_F_Natural : lower_grade (Grade F Natural) = (Grade F Minus).
    Proof. reflexivity. Qed.
    Example lower_grade_twice : lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
    Proof. reflexivity. Qed.
    Example lower_grade_thrice : lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
    Proof. reflexivity. Qed.

    Theorem lower_grade_F_Minus :
        lower_grade (Grade F Minus) = Grade F Minus.
    Proof.
        simpl. reflexivity.
    Qed.

    Theorem lower_grade_lowers :
        forall (g : grade),
        grade_comparison (Grade F Minus) g = Lt ->
        grade_comparison (lower_grade g) g = Lt.
    Proof.
        intros g H. simpl. destruct g as [l m] eqn:G.
        destruct m eqn:M.
        - simpl. rewrite letter_comparison_eq. reflexivity.
        - simpl. rewrite letter_comparison_eq. reflexivity.
        - simpl. destruct l eqn:L.
            + reflexivity. 
            + reflexivity.
            + reflexivity.
            + reflexivity.
            + rewrite H. reflexivity.
    Qed.

    Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
        if late_days <? 9 then g
        else if late_days <? 17 then lower_grade g
        else if late_days <? 21 then lower_grade (lower_grade g)
        else lower_grade (lower_grade (lower_grade g)).

    Theorem apply_late_policy_unfold :
        forall (late_days : nat) (g : grade),
        (apply_late_policy late_days g) =
            (if late_days <? 9 then g
             else if late_days <? 17 then lower_grade g
             else if late_days <? 21 then lower_grade (lower_grade g)
             else lower_grade (lower_grade (lower_grade g))).
    Proof.
        intros. reflexivity.
    Qed.

    Theorem no_penalty_for_mostly_on_time :
        forall (late_days : nat) (g : grade),
        (late_days <? 9 = true) ->
        apply_late_policy late_days g = g.
    Proof.
        intros.
        rewrite apply_late_policy_unfold.
        rewrite H.
        reflexivity.
    Qed.

    Theorem grade_lowered_once :
        forall (late_days : nat) (g : grade),
        (late_days <? 9 = false) ->
        (late_days <? 17 = true) ->
        apply_late_policy late_days g = lower_grade g.
    Proof.
        intros.
        rewrite apply_late_policy_unfold.
        rewrite H. rewrite H0. reflexivity.
    Qed.
End LateDays.


Module Binary.
    Inductive bin : Type :=
        | Z
        | B0 (n : bin)
        | B1 (n : bin).

    Fixpoint incr (m : bin) : bin :=
        match m with
        | Z => B1 Z
        | B0 n => B1 n
        | B1 n => B0 (incr n)
        end.
    
    Fixpoint bin_to_nat (m : bin) : nat :=
        match m with
        | Z => 0
        | B0 n => (bin_to_nat n) * 2
        | B1 n => (bin_to_nat n) * 2 + 1
        end.

    Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
    Proof. reflexivity. Qed.
    Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
    Proof. reflexivity. Qed.
    Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
    Proof. reflexivity. Qed.
    Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
    Proof. reflexivity. Qed.
    Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
    Proof. reflexivity. Qed.
    Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
    Proof. reflexivity. Qed.
End Binary.
