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
