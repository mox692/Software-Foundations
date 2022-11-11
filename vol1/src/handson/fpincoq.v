
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

Compute pred(S O).

(* pred n == n - 1 になることの証明 *)
Theorem pred_theorem : forall p : nat , O = O.
Proof. simpl. reflexivity. Qed.

(** Not that the type of S is nat -> nat *) 
Check S. 

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

 Compute (add (S (S O)) (S O)).

(** MEMO: using `theorem`, `forall` keywords *)
Theorem plus_O_n : forall n : nat, plus O n = n.
Proof.
  intros n. simpl. reflexivity. Qed. 







