(*********************)
(** * Basic intro    *)
(*********************)
Inductive rgb: Type := 
   red | green | blue.

Inductive color: Type := 
  black | white | primary(p: rgb). 

(* id for rgb *)
Definition rgb_id(p: rgb):rgb := p.

Example rgb_return_type_is_correct:
  rgb_id(blue) = blue.
Proof. simpl. reflexivity. Qed.

(* 上の定理を全てのrgbに適用した定理 *)
Theorem rgb_id_returns_rgb_type : forall c : rgb, rgb_id(c) = c.
Proof. simpl. reflexivity. Qed.

(** Module *)
Module Test.
  Definition test1:color := white.
End Test.

(* MEMO: CheckコマンドとComputeコマンド *)
Check Test.test1.
Compute (Test.test1).

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b0  b1 b2 b3 : bit).

Compute(bits B1 B0 B1 B0).


(* ペアノの公理に基づいた、自然数の実装 *)
Inductive nat : Type := 
  | O  
  | S(n: nat).

Check S (S O).
Compute S O.

Definition pred(n : nat) : nat := 
  match n with
  | O => O
  | S p => p
  end.

Definition succ(n : nat) : nat := S n.

(* succ n == S n になることの証明 *)
Theorem succ_theorem : forall n : nat, succ n = S n .
Proof. simpl. reflexivity. Qed.

(* TODO: pred n == n - 1 == S n になることの証明 *)
(* Theorem pred_theorem : forall p : nat , pred n = S n. *)
(* Proof. simpl. reflexivity. Qed. *)

(** Note that the type of S is nat -> nat *) 
Check S. 


(* MEMO: 再起的な関数を定義する場合 *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Fixpoint add (x: nat)(y: nat): nat :=
  match y with
  | O   => x
  | S n => add (S x) n
  end.

Fixpoint minus (n : nat)(m : nat) : nat := 
  match m with
  | O    => n
  | S n' =>
    match n with 
    | O     => O
    | S n'' => minus n'' n'
    end
  end.


Fixpoint multi_with_state(n : nat)(m : nat)(sum : nat) : nat :=
  match m with
  | O => sum
  | S m' => multi_with_state n m' (add sum n)
  end.

(* 掛け算の定義 *)
Definition multiple (n : nat)(m : nat) : nat := multi_with_state n m O.

Compute multiple  (S (S (S (S O)))) (S (S O)).

(* minusに関する定理 *)
Example minus_theorem:
  minus (S (S O)) (S O) = S O.

Proof. simpl. reflexivity. Qed.

(* + 演算子の定義 *)
Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Notation "x * y" := (multiple x y)
                      (at level 40, left associativity)
                      : nat_scope.

(* + 演算子とplus の間に成り立つ定理 *)
Theorem plus_and_plus_operator: forall x y : nat,
  x + y = plus x y.
Proof. simpl. reflexivity. Qed.

(* - 演算子と minus の間に成り立つ定理 *)
Theorem minus_and_minus_operator: forall x y : nat,
  x - y = minus x y.
Proof. simpl. reflexivity. Qed.

(*
  Proof by Case Analysis 
*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Compute  (S O) =? (S O).
Theorem plus_1_neq_0_firsttry : forall n : nat,
  (n + O) =? O = false.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_1_neq_0 : forall n : nat,
  (n + S O) =? O = false.
Proof.
  (* MEMO: desctruct の動きに注目 *)
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.


Definition negb(b : bool): bool := 
  match b with
  | true => false
  | false => true
  end.

Theorem negb_involutive: forall b : bool,
  negb(negb(b)) = b.
Proof.
  (* MEMO: bool型に対するdesctruct の動きに注目 *)
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Definition andb(x :bool)(y: bool) : bool := 
  match x with
  | false => false
  | true  => match y with
             | false => false
             | true  => true
             end
  end.

Theorem andb_commutative : forall b c,
  andb b c = andb c b.
Proof.
intros b c. destruct b eqn:Eb.
- destruct c eqn:Ec. simpl.
  + reflexivity.
  + reflexivity.
- destruct c eqn:Ec. simpl.
  + reflexivity.
  + reflexivity.
Qed.

(******************************)
(** * Proof by simplification *)
(******************************)

(* simplが使える証明. simplが何をしている？ *)
Theorem plus_1_n : forall n : nat, O + n = n.
Proof.
  intros n. cbv delta. cbv iota. cbv beta. simpl. reflexivity. Qed.


Theorem plus_1_l : forall n:nat, (S O) + n = S n.
Proof.
  intros n. simpl. reflexivity. Qed.













  Eval cbv beta in ((S O) + O).
  Check ((fun x y => x + y) (S O) ).
  Eval cbv beta in ((fun x y => x + y) (S O) O).
  Eval cbv in ((fun x y => x + y) (S O) O).
  Check ((S O) + O).







