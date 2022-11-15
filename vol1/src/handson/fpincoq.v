




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

(* 4 - 2 *)
Fixpoint minus (n : nat)(m : nat) : nat := 
  match m with
  | O    => n
  | S n' =>
    match n with 
    | O     => O
    | S n'' => minus n'' n'
    end
  end.

(* minusに関する定理 *)
Example minus_theorem:
  minus (S (S O)) (S O) = S O.

Proof. simpl. reflexivity. Qed.

(* + 演算子の定義 *)
Notation "x + y" := (plus x y)
                      (at level 50, left associativity)
                      : nat_scope.

(* + 演算子とplus の間に成り立つ定理 *)
Theorem plus_and_plus_operator: forall x y : nat,
  x + y = plus x y.

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
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.



