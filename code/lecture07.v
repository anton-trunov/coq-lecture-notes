From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** * Canonical mixins *)

Print eq_op.
(**
  eq_op = fun T : eqType => Equality.op (Equality.class T)
      : forall T : eqType, rel T

  Argument T is implicit and maximally inserted
*)

Check eqE.

Lemma eqn_back_to_eq_op n :
  eqn n n.
Proof.
rewrite -eqE.  (* *)
by [].  (* eq_refl gets applied implicitly here *)
Qed.

(** A bigger example: *)
Lemma baz (n m : nat) (b : bool) (p: prod bool nat) (o : option nat) :
  (Some n.+1 == Some n.+1)
  && (b == b) && (p == (false, 0))
  && (Some 2 == o) && (o == Some 2)
  .
Proof.
  (* move=>/=. *)
  (* rewrite /eq_op. *)
  (* simpl. *)
  (* rewrite /eq_op. *)
  (* simpl. *)
(** [move=>/=]. would not really simplify *)
do ! rewrite !eqE /= -!eqE.
rewrite !eq_refl /=.

Undo 2.

do ! rewrite !eqE /=.
Fail rewrite eq_refl.
rewrite -!eqE.
rewrite !eqE.
rewrite /=.
rewrite -!eqE.
Abort.


(** How does folding back with [rewrite -eqE] work? *)
About eqE.

(* Check eqE. *)
(* Print nat_eqMixin. *)
(* Check Equality.class. *)
(* done. *)

(**

1) Let's match the goal with the rewrite lemma

     eqn                              n     n
===
     Equality.op (Equality.class ?T) ?x

2) Then focus on the head symbol

     eqn
===
     Equality.op (Equality.class ?T)

3) We have a unification equation of the form
     Equality.op ?something === eqn

Have we got a canonical projection for this?
Let's look in our table:
*)

Print Canonical Projections. (** eqn <- Equality.op ( nat_eqMixin ) *)


(** Just a reminder what [nat_eqMixin] is *)
(* Set Printing All. *)
Print nat_eqMixin.   (** @Equality.Mixin nat eqn (@eqnP) *)
(* Unset Printing All. *)


(**

3) Now we know ?something is (Equality.class ?T)


     (Equality.class ?T)    : Equality.mixin_of (?T : eqType)
===
     nat_eqMixin            : Equality.mixin_of nat

[Equality.class] is not in the table of canonical projections.
Are we stuck?


4) Let's add type annotations!


     (Equality.class ?T)    : Equality.mixin_of (?T : eqType)
===
     nat_eqMixin            : Equality.mixin_of nat


5) This we already know how to solve!


    (?T : eqType)
====
    nat

*)




(** * Phantom types *)

(**

Idiom:
A function with one or more dummy arguments + [Eval hnf].

The dummy arguments serve to trigger and/or constrain type inference.
This can fire up canonical structure search, or projection out of a record type and many more things.

[Eval hnf] is needed to get rid of those dummy argument(s).
*)



(** ** A concrete example *)

About allP.

(**
    allP :
    forall (T : eqType) (a : pred T) (s : seq T),
    reflect {in s, forall x : T, a x} (all a s)

{in s, forall x : T, a x} means
(forall x : T, x \in s -> a x)
*)

(** A simple example of how [_ \in _] can be used. *)
Check erefl : 2 \in [:: 1; 2; 3] = true.

Definition n_is_2 := pred1 2.  (** equiv. to (_ == 2) *)
Check erefl : 2 \in n_is_2 = true.
Check erefl : 0 \in n_is_2 = false.

(**
So, what's the challenge with {in s, forall x : T, a x}?


The challenge is to transform an unknown universally
quantified proposition into a new one, i.e.
to go from [forall x : T, a x] to
[forall x : T, x \in s -> a x]

This is something not possible using simple notations,
unless we are willing to repeat Coq's syntax to
a certain extent.

Notation "{ 'in' d , P }" :=
  (... stuck because [forall] is inside [P]
       and we wouldn't want to redefine [forall] syntax ...).
*)

(** With phantom types we can sort of pattern-match on
    the form of a type, just like we did before with the
    form of a term.
    Once we have the components of e.g. a proposition, we
    can rearrange those into a new one, possibly adding
    more logical connectives.
*)


(** But first let's turn to a simpler example. *)

Definition conj_swap A B
           (_ : phantom Prop (A /\ B)) : Prop :=
  B /\ A.
Notation "'{' '/|\' p '}' " :=
  (@conj_swap _ _ (Phantom Prop p)).

(** Usage: *)
Eval hnf in { /|\ False /\ True}.
(**
     = True /\ False
     : Prop
*)

(** We can go even deeper and generalize the above to
    (almost) arbitrary binary logical connectives: *)
Definition bin_conn_swap A B
           (conn : Prop -> Prop -> Prop)
           (_ : phantom Prop (conn A B)) : Prop :=
  conn B A.

Notation "'{' '|' p '}' " :=
  (@bin_conn_swap _ _ _ (Phantom Prop p)).

Eval hnf in { | False /\ True}.
Eval hnf in { | False \/ True}.

Fail Eval hnf in { | True}.


(** A couple of exceptions *)
Eval hnf in { | False <-> True}.
(** strips away [iff] _definition_ *)

Fail Eval hnf in { | False -> True }.
(** [x -> y]  means [forall (_ : x), y] *)


(** ** How does this example work? *)

Print phantom.
(**
    Variant phantom (T : Type) (p : T) : Prop :=
      | Phantom : phantom T p
*)

(* [Phantom] constructor is used
   to lift terms at the level of types *)
Check Phantom nat 42 : phantom nat 42.


Eval hnf in { | False /\ True}.
(*
This is how unification goes here (notation unfolded):

(@bin_conn_swap _  _  _     (Phantom Prop (and False True) : phantom Prop (and   False True))).
(@bin_conn_swap ?A ?B ?conn (_                             : phantom Prop (?conn ?A    ?B  ))).
*)

(**
Note: we could have utilized a simpler version of
[phantom] used when dealing with types, not terms:

  Definition bin_conn_swap A B
            (conn : Prop -> Prop -> Prop)
            (_ : phant (conn A B)) : Prop :=
    conn B A.
  Notation "'{' '|' p '}' " :=
    (@bin_conn_swap _ _ _ (Phant p)).

 *)


(** Let us go back and see how {in d, P} notation
    can be implemented *)

Definition
  prop_in1
  (T1 : Type)
  (d : mem_pred T1)
  (P : T1 -> Prop)
  & phant (forall x : T1, P x)
  : Prop :=
     forall x : T1, x \in d -> P x.

Notation "{ 'in' d , P }" :=
  (prop_in1 (mem d) (Phant P)).

Print phant.
Check Phant nat : phant nat.

Section example_usage.
Variables
  (T : eqType) (a : pred T) (s : seq T).

Eval hnf in {in s , forall x, a x}.

(**
     = forall x : T, x \in mem s -> a x

Note:
[seq] is an instance of [predType] -- the generic
predicate interface, supported e.g. for for lists
and sets.
This can be analyzed using the following vernacular.
  Set Printing Coercions.
  Check mem.
  Print Canonical Projections.
We look for [list <- pred_sort ( seq_predType )] entry here.
*)

End example_usage.



(** * Cloning constructors *)


(**
Cloning constructors are mainly used to quickly
create instances for defined types, such as

    Definition bitseq := seq bool.

While [seq] provides an instance of [eqType],
type inference needs to synthesize an [eqType] structure for
[bitseq] and Coq has to expand the definition of
[bitseq] to do so.
Declaring [bitseq]-specific instance will avoid
such spurious expansions, and is easy thanks to
cloning constructors, e.g.

    Canonical bitseq_eqType :=
      Eval hnf in [eqType of bitseq].

*)

(**
    Definition clone :=
      fun c & cT -> T & phant_id (@Pack T c) cT =>
        Pack c.

    Notation "[ 'eqType' 'of' T ]" :=
      (@clone T _ _ id id).
*)

Print phant_id.
(**
    phant_id = fun (T1 T2 : Type) (v1 : T1) (v2 : T2) =>
      phantom T1 v1 -> phantom T2 v2
        : forall T1 T2 : Type, T1 -> T2 -> Prop

    Arguments T1, T2 are implicit
*)

Eval hnf in [eqType of bitseq].

(**
     = EqType bitseq (seq_eqMixin bool_eqType)
     : eqType
*)

(** ** How does it work? *)

(**
[eqType of bitseq]

unfolds into

@Equality.clone bitseq _ _ id id
*)

About Equality.clone.
(**
forall
(T : Type)
(cT : eqType)
(c : Equality.mixin_of T),
(cT -> T) ->
phant_id (EqType T c) cT ->
eqType
*)

(**
@clone bitseq      _              _                (id : ?A -> ?A) (id : ?B -> ?B)
       (?T : Type) (?cT : eqType) (c : mixin_of T) (_  : cT -> T ) (_  : phant_id (EqType T c) cT)


@clone bitseq      _              _                (id : ?A       -> ?A)  (id : ?B                     -> ?B          )
       (?T : Type) (?cT : eqType) (c : mixin_of T) (_  : sort ?cT -> ?T ) (_  : phantom _ (EqType T c) -> phantom _ cT)

Unification equations:
?T === bitseq                                       (or ?T === seq bool)
sort ?cT === ?T                                     (triggers canonical structure search)
?A -> ?A === sort ?cT -> ?T                         (basically, sort ?cT === ?T)
?B -> ?B === phantom _ (EqType T c) -> phantom _ cT (basically, EqType T c === cT, i.e. we extract mixin from cT)

Upshot: using phantoms we can extract components out of concrete structures.
*)




(** Bonus:
    On-the-fly eta expansion and
    Miller pattern unification *)

Lemma compA A B C D (f : A -> B) (g : B -> C) (h : C -> D):
  (h \o g) \o f = h \o (g \o f).
Proof. by []. Qed.

Lemma compAtest A (f : A -> A) :
  f \o f =1 f.
Proof.
(** vanilla Coq [rewrite] works as expected *)
Fail rewrite -> compA.

(* ssrelfect [rewrite] introduces [id] *)
rewrite compA.
(** this goes on indefinitely *)
rewrite 5!compA.
Undo 2.

(**
What is going on here?
Let's match the goal with the LHS of the equation:

               f \o f  =1 f
      (?h \o ?g) \o ?f

Unification equations:
?f === f                   (trivial)
?h \o ?g === f             (let's focus on this one)

(fun x => ?h (?g x)) === f

we use eta expansion to make sure [f] has the same form as
the LHS:

(fun x => ?h (?g x)) === (fun x => f x)

?h (?g x) === f x

?h === f
?g x === x

?h := f
?g := id
?f := f

               f \o f =1 f expands to
       (f \o id) \o f =1 f which after rewriting turns into
       f \o (id \o f) =1 f

*)
Abort.
