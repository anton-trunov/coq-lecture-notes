From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** Universal
     quantifier *)

(** * Motivation *)

(** Suppose we wrote two functions: a simple (a.k.a. gold) implementation
    and its optimized version.
    How do we go about specifying their equivalence?
 *)

Section Motivation.
Variables A B : Type.

Variables fgold fopt : A -> B.

Lemma fopt_equiv_fgold :
  forall x : A, fgold x = fopt x.
Abort.

End Motivation.



(** * Dependently typed functions *)

(** ** Dependently typed predecessor function *)

Definition Pred n := if n is S n' then nat else unit.

(** the value of [unit] type plays the role of a placeholder *)
Print unit.

Definition predn_dep : forall n, Pred n :=
  fun n => if n is S n' then n' else tt.

Check erefl : predn_dep 7 = 6.
Fail Check erefl : predn_dep 0 = 0.
Check erefl : predn_dep 0 = tt.
Check predn_dep 0 : unit.
Check erefl : Pred 0 = unit.
Check predn_dep 7 : nat.


(** ** Annotations for dependent pattern matching *)

(** Type inference is undecidable *)
Fail Check (fun n => if n is S n' then n' else tt).

Check (fun n =>
  if n is S n' as n0 return Pred n0 then n' else tt).

(**
General form of pattern matching construction:
[match expr as T in (deptype A B) return exprR].

- [return exprR] denotes the dependent type of the expression
- [as T] is needed when we are matching on complex expressions,
  not just variables
*)



(** * Functional type is just a notation
      for a special case of [forall]  *)

Locate "->".

Check predn : nat -> nat.
Check predn : forall x : nat, nat.
Check predn : forall x : nat, (fun _ => nat) x.


(** * Usage of [forall] in standalone expressions *)

(* courtesy of Mathcomp book *)
Section StandardPredicates.
Variable T : Type.
Implicit Types (op add : T -> T -> T).

Definition associative op :=
  forall x y z, op x (op y z) = op (op x y) z.

Definition left_distributive op add :=
  forall x y z, op (add x y) z = add (op x z) (op y z).

Definition left_id e op :=
  forall x, op e x = x.

End StandardPredicates.



(** * Case study: the dual Frobenius rule *)

(* Due to Andrej Bauer:
https://github.com/andrejbauer/Homotopy/blob/8474551e28ceeeba4910370326dc3ffd5e340f09/OberwolfachTutorial/frobenius.v#L53-L58 *)

Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Lemma lem_implies_Frobenius2 : LEM -> Frobenius2.
Proof.
rewrite /LEM /Frobenius2.
move=> lem.
move=> A P Q.
split.
- move=> all_qpx.
  case: (lem Q); first by move=> q; left.
  move=> nq. right. move=> x.
  case: (all_qpx x); first by move/nq.
  by [].
case; first by move=> q x; left.
by move=> all_px x; right.

Restart.

move=> Lem A P Q.
case: (Lem Q)=> [q | not_q]; first by split=> _; left.
split=> [H | [//|x px]]; last by right.
by right=> x; case: (H x).
Qed.

Lemma Frobenius2_lem : Frobenius2 -> LEM.
Proof.
rewrite /Frobenius2=> frob.
move=> P.
case: (frob P (fun _ => False) P).
move=> H _; move: H.
by apply=> p; left.
Qed.


(*** Existential
     quantifier *)
Module MyExistential.

Inductive ex_my (A : Type) (P : A -> Prop) : Prop :=
| ex_intro (x : A) (proof : P x).

(** Simplified notation *)
Notation "’exists’ x : A , p" := (ex (fun x : A => p))
                                   (at level 200, right associativity).

(** Full-blown notation: multiple binders *)
Notation "'exists' x .. y , p" :=
  (ex_my (fun x => .. (ex_my (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
End MyExistential.


Lemma exists_not_forall A (P : A -> Prop) :
  (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
case=> x px.
move=> all.
exact: (all x px).
Qed.

(** Currying for dependent pair *)
Definition curry {A B C : Type} :
  (A * B -> C) -> (A -> B -> C).
move=> f a b.
exact: (f (pair a b)).
Defined.

Lemma curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q).
Proof.
move=> f x px.
exact: (f (ex_intro _ x px)).
Qed.


Section Symmetric_Transittive_Relation.

Variables (D : Type) (R : D -> D -> Prop).

(* [Hypothesis] is a different syntax for [Variable] *)
Hypothesis Rsym :
  forall x y, R x y -> R y x.

Hypothesis Rtrans :
  forall x y z, R x y -> R y z -> R x z.

Lemma refl_if :
  forall x : D, (exists y, R x y) -> R x x.
Proof.
move=> x.
case=> y rxy.
move: (Rsym rxy); move: rxy.
by apply: Rtrans.
Qed.

End Symmetric_Transittive_Relation.



(*** Empty types,
     again *)

Lemma exfalso_quodlibet :
  False -> forall P : Prop, P.
Proof. by []. Qed.

(** Let's write down a proof term manually *)
Definition exfalso_quodlibet_term :
  False -> forall P : Prop, P
:=
  fun f =>
    match f with end.

(** A special case of exfalso. *)
(** Why does this typecheck at all? *)
Lemma False_implies_false :
  False -> false.
Proof. by case. Qed.


(** * Disjointness of constructors *)

(** Going in the other direction... *)
Lemma false_implies_False :
  false -> False.
Proof. by []. Qed.

(** What's going on here? Let's write a proof term *)
Check I : True.

Definition false_implies_False_term :
  false -> False
:=
  fun     eq :  false = true =>
    match eq in (_    = b)
             return (if b then False else True)
    with
    | erefl => I
    end.


(** * Injectivity of constructors *)

(** While we are at it,
    constructors are also injective *)
Lemma succ_inj n m :
  S n = S m -> n = m.
Proof.
case. (* special case for [case] *)
Show Proof.
done.
Qed.

Lemma pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2).
Proof. by case=> ->->. Qed.



(*** Induction *)

Lemma addnA :
  associative addn.
Proof.
by move=> x y z; elim: x=> // x IH; rewrite addSn IH.
Qed.

Lemma add0n :
  left_id 0 addn.
Proof. by []. Qed.

Lemma addn0 :
  right_id 0 addn.
Proof. by elim=> // x IH; rewrite addSn IH. Qed.

Lemma addSnnS m n :
  m.+1 + n = m + n.+1.
Proof. by elim: m=> // m IH; rewrite addSn IH. Qed.

Lemma addnC :
  commutative addn.
Proof.
move=> x y.
elim: x; first by rewrite addn0.
by move=> x IH; rewrite addSn IH -addSnnS.
Qed.

(** * How does induction work? *)

Check nat_ind.

Definition nat_ind_my
  : forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P n.+1) ->
    forall n : nat, P n
:=
  fun P p0 step =>
    fix rec n :=
      if n is n'.+1 then step n' (rec n')
      else p0.

(** Induction is just recursion! *)
