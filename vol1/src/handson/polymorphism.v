From LF Require Export Lists.
(* ここから *)

Inductive list(X: Type) :=
    | nil
    | cons(x : X)(l : list X)
    .

Compute (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.

(* Type -> Type で、 Xを受け取って、何かしらの(List関連の)型を返す *)
Check list.
(* List X 型  *)
Check nil.
(* List nat 型*)
Check nil nat.
(* X -> list X -> list X 型*)
Check cons.
Check cons nat.
Check cons nat O.
Check cons
        nat (* 型引数 *)
        O   (* head の要素 *)
        (nil nat). (* tail の要素. nilにも型注釈をつける. *)

Check cons
        nat
        O
        (cons
            nat
            (S O)
            (nil nat)).

Check (cons nat 2 (cons nat 1 (nil nat))).

(* Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
end. *)

Check cons.
(* 多相型の関数定義の例 *)
Fixpoint repeat'(X : Type)(x : X)(times : nat) : list X :=
    match times with
    | 0    => nil X
    | S n' => cons X x (repeat' X x n')
    end
.

Check nil nat.

(* TODO: なんでアンスコで書かないといけない？？ *)
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil _ => l2
  | cons _ h t => cons _ h (app t l2)
  end.
(* MEMO: この app のシグネチャがヒントかも *)
Check app.

(* Arguments nil {X}.
Arguments cons {X}. *)
Fixpoint rev(X: Type)(l : list X): list X := match l with 
    | nil _  => nil _
    | cons _ h t => app (rev _ t) (cons _ h (nil _))
    end
.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil _ => 0
  | cons _ h t => S (length t)
  end.

Check length (cons nat 3 (nil nat)).
Check length (cons _ 3 (nil _)).


Arguments nil {X}.
Arguments cons {X}.
(* Arguments repeat {X}. *)

Fail Definition mynil := nil.
Definition mynil : list nat := nil.
Definition mynil' := @nil nat.
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** Exercise: 2 stars, standard (poly_exercises) *)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l.
  * reflexivity. 
  * simpl. 
    rewrite -> IHl.
    reflexivity.
  Qed.

(* simpl. が仕事しすぎていて何をしているのかわからん *)
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  * simpl.
    reflexivity.
  * simpl. 
    rewrite -> IHl.
    reflexivity.
  Qed.

(* Polymorphic Pairs *)
Inductive prod(X Y: Type) : Type :=
  pair(x : X)(y : Y).

(* example *)
Compute pair nat bool 4 false.

Arguments pair {X} {Y}.

(* 上のArguments の効果 *)
Compute pair 3 false.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Compute (4, false).

Definition fst(X : Type)(Y : Type)(v : prod X Y) : X :=
  match v with
  | pair x y => x
  end
.

Definition fst2{X Y : Type}(v : prod X Y) : X :=
  match v with
  | pair x y => x
  end
.

Definition snd(X : Type)(Y : Type)(v : prod X Y) : Y :=
  match v with
  | pair x y => y
  end
.

Definition snd2{X Y : Type}(v : prod X Y) : Y :=
  match v with
  | pair x y => y
  end
.

Compute fst nat nat (3, 4).
Compute fst2 (3, 4).
Compute snd nat bool (4, false).

Fixpoint zip(X : Type)(Y : Type)(l1 : list X)(l2 : list Y): list (prod X Y) :=
  match l1 with
  | nil => nil
  | cons h t =>
    match l2 with
    | nil => nil
    | cons h' t' => (h, h') :: zip X Y t t'
    end
  end
.

Compute zip nat nat [1;2;3] [4;5;6].

(* Polymorphic Options *)
Inductive option(X : Type) : Type :=
  | none
  | some(x : X)
  .

Arguments some {X}.
Arguments none {X}.

Definition headOption{X : Type}(l : list X) : option X :=
    match l with
    | nil => none
    | cons h t => some h
    end
.

Compute headOption (cons 3 nil).
Compute headOption nil.

(* Functions as Data *)
Definition double(n : nat) : nat := n * 2.
Definition do3times{A : Type}(a : A)(f: A -> A) : A := f (f (f a)).


(* Filter *)
Fixpoint filter{X : Type}(l : list X)(f : X -> bool) : list X :=
  match l with
  | nil => l
  | cons h t =>
    match (f h) with
      | true => cons h (filter t f)
      | false => filter t f
    end
  end
.

Fixpoint is_odd(n : nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S n' => is_odd(n' - 1)
  end
.

Compute filter([1;2;3])(is_odd).































