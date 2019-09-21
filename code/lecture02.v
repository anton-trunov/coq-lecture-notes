From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

Set Implicit Arguments.

Module MyNamespace.

(** Euclidean division: returns quotient and reminder  *)

(** Type constrtuctors, Product type *)

Section ProductType.

Inductive prod (A B : Type) : Type :=
  | pair of A & B.

About pair.

(** Explicit binding of type constructor's parameters for
    data constrtuctors
  *)
Check pair 42 true : prod nat bool.

(** Implicit arguments;
    local deactivation of implicit arguments (@)
 *)

Fail Check pair nat bool 42 true : prod nat bool.  (* inconvenient *)
Check @pair nat bool 42 true.




(** Notations for better UX *)

Notation "A * B" := (prod A B) (at level 40, left associativity) : type_scope.



(** Notation scopes *)

Fail Check nat * bool.

Check (nat * nat)%type.

Check (nat * bool) : Type.

Open Scope type_scope.
Check (nat * nat).
Close Scope type_scope.
Fail Check (nat * nat).

(** Left / right associativity *)
Check ((nat * bool) * nat)%type.

Check (nat * (bool * nat))%type.

(** Weak notatiton *)
Notation "( p ; q )" := (pair p q).

(** Triples, quadruples, ... ? *)

(** Recursive notations *)

Notation "( p , q , .. , r )" := (pair .. (pair p q) .. r)
                                   : core_scope.

Check (1, false) : nat * bool.

Unset Printing Notations.
Check (1, false) : nat * bool.
Set Printing Notations.

Definition fst {A B : Type} : A * B -> A :=
  (* fun p => match p with | pair a b => a end. *)
  (* fun p => let (a, b) := p in a. *)
  fun '(a, _) => a.

Notation "p .1" := (fst p).

Definition snd {A B : Type} : A * B -> B :=
  fun '(a, b) => b.

Notation "p .2" := (snd p).

Definition swap {A B : Type} : A * B -> B * A :=
  fun '(a,b) => (b,a).

End ProductType.

(**
      A /\ B -> B /\ A
 *)

Check fst.
Check snd.
Check @pair _ _.


Section Intuitionistic_Propositional_Logic.

(** Implication *)

Definition A_implies_A (A : Prop) :
  A -> A
:=
  fun proof_A : A => proof_A.

Definition A_implies_B_implies_A (A B : Prop) :
  A -> B -> A
:=
  fun proof_A => fun proof_B => proof_A.
(* const *)


(** Conjunction *)

Inductive and (A B : Prop) : Prop :=
  | conj of A & B.

Notation "A /\ B" := (and A B) : type_scope.

Definition andC (A B : Prop) :
  A /\ B -> B /\ A
:=
  fun '(conj proof_A proof_B) => conj proof_B proof_A.

Definition andA (A B C : Prop) :
  (A /\ B) /\ C -> A /\ (B /\ C)
:=
  fun '(conj (conj a b) c) => conj a (conj b c).


(** Biimplication, a.k.a. if and only if *)

Definition iff (A B : Prop) : Prop :=
  (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Definition andA_iff (A B C : Prop) :
  (A /\ B) /\ C <-> A /\ (B /\ C)
:=
  conj
    (fun '(conj (conj a b) c) => conj a (conj b c))
    (fun '(conj a (conj b c)) => (conj (conj a b) c)).


(** Disjunction *)

Inductive or (A B : Prop) : Prop :=
| or_introl of A
| or_intror of B.

Arguments or_introl [A B] a, [A] B a.
Arguments or_intror [A B] b, A [B] b.

Notation "A \/ B" := (or A B) : type_scope.

Definition or1 (A B : Prop) : A -> A \/ B
  :=
fun proofA => or_introl proofA.

Definition orC A B :
  A \/ B -> B \/ A
:=
  fun a_or_b =>
    match a_or_b with
    | or_introl proofA => or_intror proofA
    | or_intror proofB => or_introl proofB
    end.

Definition or_and_distr A B C :
  (A \/ B) /\ C -> (A /\ C) \/ (B /\ C)
:=
  fun '(conj a_or_b c) =>
    match a_or_b with
    | or_introl a => or_introl (conj a c)
    | or_intror b => or_intror (conj b c)
    end.

Inductive False : Prop := .

Inductive True : Prop :=
  | I.

Definition t : True
  :=
I.

Definition t_and_t : True /\ True
  :=
conj I I.

Definition not (A : Prop) :=
  A -> False.

Notation "~ A" := (not A) : type_scope.

Definition A_implies_not_not_A (A : Prop) :
   A -> ~ ~ A
(* A -> (A -> False) -> False *)
:=
  fun a => fun not_a => not_a a.

(* Double negation elimination is
   not provable in Intuitionistic Logic *)
Fail Definition DNE (A : Prop) :
   ~ ~ A -> A
:=
  fun nna => __.  (* can't call [nna] *)

(* Since the Law of Exlcluded Middle
   is equivalent to DNE it's not provable
   either
 *)
Fail Definition LEM (A : Prop) :
   A \/ ~A
:=
  (* or_intror (fun a => ???). *)
  __. (* or_introl / or_intror ? *)

End Intuitionistic_Propositional_Logic.


Section Propositional_Equality.

Inductive eq (A : Type)
             (a : A) : A -> Prop :=
| eq_refl : eq a a.
Check eq_ind.

About eq.
Check eq_refl 1 : eq 1 1.
Fail Check eq_refl 1 : eq 1 21.

Check @eq_refl nat 2 : @eq nat 2 2.
Fail Check eq_refl 1 : @eq nat 1 2.
Fail Check eq_refl 2 : @eq nat 1 2.

Notation "a = b" := (eq a b) : type_scope.


Definition eq_reflexive A (x : A) :
  x = x
:=
  eq_refl x.

(* dependent pattern matching *)
Definition eq_sym A (x y : A) :
  x = y -> y = x
:=
  fun proof_x_eq_y =>
    match proof_x_eq_y with
    | eq_refl => eq_refl x
    end.

Definition eq_foo (x y z : nat) :
  x + y = y + z -> (x + y) + z = (y + z) + z
:=
  fun prf_eq =>
    match prf_eq with
    | eq_refl => eq_refl ((x + y) + z)
    end.

Definition eq_trans A (x y z : A) :
  x = y -> (y = z -> x = z)
:=
  fun x_eq_y : x = y =>
    match x_eq_y with
    | eq_refl => id
    end.

End Propositional_Equality.

End MyNamespace.


(** The SSReflect proof language *)

Lemma A_implies_A (A : Prop) :
  A -> A.
Proof. (* <-- optional *)
Show Proof.
move => a.   (* tactical *)
Show Proof.
(* move: a. exact. *)
exact: a.
Show Proof.
(* by []. *)
Qed.

Lemma or_and_distr A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case.
- move=> a. move=> c. left. split.
  - exact: a.
  by apply: c.
move=> b c. right. by split.
Qed.

About or_and_distr.


(* a terser version *)
Lemma or_and_distr' A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
by move=> [[a | b] c]; [left | right].
Qed.

(* An example taken from
"An Ssreflect Tutorial" by G.Gonthier, R.S. Le(2009)
 *)
Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> hAiBiC hAiB hA.
move: hAiBiC.
apply.
- by [].
by apply: hAiB.
Qed.

End HilbertSaxiom.

Section Rewrite.

Variable A : Type.
Implicit Types x y z : A.

Lemma eq_reflexive x :
  x = x.
Proof. by []. Qed.


Lemma eq_sym x y :
  x = y -> y = x.
Proof.
move=> x_eq_y. rewrite -x_eq_y. by [].
Show Proof.
Qed.
Eval compute in eq_sym.

Lemma eq_sym_shorter x y :
  x = y -> y = x.
Proof.
by move=> ->.
Qed.

Lemma eq_trans x y z :
  x = y -> y = z -> x = z.
Proof.
move=> ->->.
apply: eq_reflexive.
Qed.
