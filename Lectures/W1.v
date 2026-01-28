(** Week-1: 
- Simple, compound, inductive data types
- Recursive functions
- Proof by Simplification, Proof by Case Analysis
- Ref: Software Foundations Vol.1, Basics.v
*)

(**

Gallina: the specification and programming language for Rocq

- A small core functional language
- Even basic data types such as integers, booleans, strings, etc.
 are not part of the core language!
- Provides a mechanism to build user-defined types

**)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(**
- monday, tuesday, etc. are also called constructors.
- They are used to construct values of the type.

**)

(**
- In a functional language, there is no mutable state.
- All functions are pure: they consume arguments and produce values
**)

Definition a_day : day := wednesday.

Compute a_day.

Definition next_working_day (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.
  
(**
"match <> with |" : also known as pattern matching
**)
  
Compute (next_working_day a_day).
(* ==> monday : day *)

Compute (next_working_day (next_working_day saturday)).
(* ==> tuesday : day *)

(**
Homework: Define a function prev_working_day.
**)

(** Booleans **)

(** Following the pattern of the days of the week above, we can
    define the standard type [bool] of booleans, with members [true]
    and [false]. *)

Inductive bool : Type :=
  | true
  | false.

(** Functions over booleans can be defined in the same way as
    above: *)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
  
Definition andb_alternate1 (b1: bool) (b2: bool) : bool :=
  match b1,b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => false
  end.
   
  
(**
In Rocq, all functions must be total.
- That is, they must be defined for all values of their arguments.


Definition andb_alternate2 (b1: bool) (b2: bool) : bool :=
  match b1,b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  end.
**)
  
Definition andb_alternate2 (b1: bool) (b2: bool) : bool :=
  match b1,b2 with
  | true,true => true
  | _,_ => false
  end.

(**
Underscore (_) are called wildcard patterns. They match with any value.
**)


Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.
  
Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.
  
(**
- If conditionals are similar to those used in other languages, with one difference.
- Recall that booleans are not built-in types in Rocq.
- If the conditional expression evaluates to the first constructor, then the if-branch 
is taken.
- Otherwise, the else-branch will be taken. 
**)

Inductive bw : Type :=
  | bw_black
  | bw_white.

Definition invert (x: bw) : bw :=
  if x then bw_white
  else bw_black.

Compute (invert bw_black).

(**
Compound Data-types

- Built using existing data types
**)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(**
- red, green, blue are values of type rgb.
- black, white are values of type color.
- (primary p) is a value of type color, where p is a value of type rgb.
**)

Definition a_color := primary red.

Compute a_color.

Check primary.

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
  
Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
  
(** Inductive Data types **)

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).
  
(**
- O, S O, S (S O), S (S (S O)), ... are all values of type nat.
- There are an infinite number of such values.
**)

Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

(**
- Note that the names of the constructors are not important.
- Their structure and meaning is more critical.
- What are values of type otherNat?
**)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Compute (pred (S O)).
Compute (pred (S (S O))).
Compute (pred (S (S (S O)))).

End NatPlayground.

(** nat is defined as a Rocq library, and hence can be freely used. **)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).

(** Recursive functions **)

Fixpoint even (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => even n'
  end.
  
Definition odd (n: nat) := negb (even n).

(**
Homework: Write a recursive definition of odd without using even.
**)

Compute (even 4). 
Compute (odd 10).

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(** Adding three to two gives us five (whew!): *)

Compute (plus 3 2).
(* ===> 5 : nat *)

(** The steps of simplification that Coq performs here can be
    visualized as follows: *)

(*      [plus 3 2]
   i.e. [plus (S (S (S O))) (S (S O))]
    ==> [S (plus (S (S O)) (S (S O)))]
          by the second clause of the [match]
    ==> [S (S (plus (S O) (S (S O))))]
          by the second clause of the [match]
    ==> [S (S (S (plus O (S (S O)))))]
          by the second clause of the [match]
    ==> [S (S (S (S (S O))))]
          by the first clause of the [match]
   i.e. [5]  *)
   
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Compute (mult 3 3).

End NatPlayground2.

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

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
  
(** Proofs in Rocq 
- Proof by Simplification

**)

Set Printing All.

Theorem plus_1_1 : 1 + 1 = 2.
Proof. simpl. reflexivity. Qed.

Unset Printing All.

(** 
- simpl applies the definition of functions to simplify an expression.
- reflexivity proves the syntactic equality of expressions
  * Constructors with the same name and same arguments
  * Function applications with the same function name and the same arguments.
 **)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. simpl. reflexivity. Qed.

Theorem plus_id_example : forall n m: nat, n = m -> n + n = m + m.
Proof. intros n m.
intros H.
rewrite <- H.
reflexivity.
Qed.

(**
- rewrite -> H tactic changes the goal by using the equality in H from left to right.
**)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
intros n m o.
intros H1 H2.
rewrite -> H1.
rewrite <- H2.
reflexivity. Qed.
  
(** The [Check] command can also be used to examine the statements of
    previously declared lemmas and theorems.  The two examples below
    are lemmas about multiplication that are proved in the standard
    library.  (We will see how to prove them ourselves in the next few lectures)
*)

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)

Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

(* Homework: Prove that
forall n m : nat, m + (n * m) = (S n) * m
 *)
  
Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
  
(** Proof by Case Analysis **)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
intros n. destruct n as [| m] eqn:E.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

(** 
- destruct n performs case analysis by considering every possible form of n.
- The annotation "[as [| m]]" is called an _intro pattern_.  
It tells Coq what variable names to introduce in each subgoal.
- The [eqn:E] annotation tells [destruct] to give the name [E] to the equation obtained
by destructing n.
- The "-" signs on the second and third lines are called _bullets_,
and they mark the parts of the proof that correspond to the two
generated subgoals. 
**)

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.  Qed.

Theorem and_commutative: forall b1 b2 : bool, andb b1 b2 = andb b2 b1.
Proof.
 intros b1 b2. destruct b1 eqn:E1.
 - destruct b2 eqn:E2.
   * reflexivity.
   * reflexivity.
 - destruct b2 eqn:E2.
   * reflexivity.
   * reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof. intros b c. destruct b eqn:E1.
- destruct c eqn: E2.
  * reflexivity.
  * simpl. intros H. rewrite H. reflexivity.
- destruct c eqn: E2.
  * reflexivity.
  * simpl. intros H. rewrite H. reflexivity.
Qed.

(* An issue with proving termination of a recursive function *)

(** Fixpoint plus' (n m: nat) : nat :=
match n with
| O => m
| S n' => S (plus' m n')
end.
**)




