From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** [reflect] predicate *)

Section MotivationalExample.

Variable T : Type.

Variable p : pred T.
Print pred.
Check p : T -> bool.

Lemma all_filter (s : seq T) :
  all p s -> filter p s = s.
Proof.

(* Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C) s) *)

Print filter.
Print all.

elim: s => //= x s IHs.

rewrite /is_true.
move=> /andP.
(* Set Printing Coercions. *)
rewrite /is_true.
move=> [].
move=> ->.
move/IHs.
move=>->.
done.

Restart.

by elim: s => //= x s IHs /andP[-> /IHs->].
Qed.

End MotivationalExample.


(** How does [andP] from above work? *)

About andP.

Print reflect.
Print Bool.reflect.

(**
    Inductive reflect (P : Prop) : bool -> Set :=
    | ReflectT : P -> reflect P true
    | ReflectF : ~ P -> reflect P false
 *)

Search _ reflect.

(** First, let us show that [P] if and only if [b = true]
    as two separate lemmas
  *)

Lemma introT_my (P : Prop) (b : bool) :
  reflect P b -> P -> b.
Proof.
Set Printing Coercions.
rewrite /is_true.
Unset Printing Coercions.
case.
- move=> _ _. done.
move=> np. move/np. case.
Qed.

Lemma elimT_my (P : Prop) (b : bool) :
  reflect P b -> b -> P.
Proof.
case.
- move=> p _. exact: p.
move=> _. done.
Qed.

  (* reflect P b -> (b <-> P). *)

(** Essentially, a [reflect] predicate connects
    a _decidable_ proposition to its decision procedure.
 *)
Lemma reflect_lem P b :
  reflect P b -> P \/ ~ P.
Proof.
by case=> H; [left | right].
Qed.

(** Lets look at some standard [reflect] predicates *)

Lemma andP_my (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
by case: b; case: c; constructor=> //; case.
Qed.


Lemma orP_my (b c : bool) :
  reflect (b \/ c) (b || c).
Proof. (* exercise *) Admitted.

Lemma nandP_my b c : reflect (~~ b \/ ~~ c) (~~ (b && c)).
Proof. by case: b; case: c; constructor; auto; case. Qed.



(** * Using reflection views in intro patterns *)

Lemma special_support_for_reflect_predicates b c :
  b && c -> b /\ c.
Proof.
move/andP.
Show Proof.

(**
SSReflect implicitly inserts the so-called view hints to
facilitate boolean reflection. In this case it's [elimTF] view hint.

Here is the syntax to do that (see ssrbool.v file):
Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.

The optional natural number is the number of implicit arguments
to be considered for the declared hint view lemma.

The ssrbool.v module already declares a numbers of view hints,
so adding new ones should be justtified. For instance, one might need to do it
if one defines a new logical connective.
 *)

(* Set Printing All. *)
(* Show Proof. *)

About introTF.
About elimTF.
About elimF.

Restart.

move=> Hb.
Check @elimTF (b /\ c) (b && c) true (@andP b c) Hb.
move: Hb.
move/(@elimTF (b /\ c) (b && c) true (@andP b c)).

exact: id.
Qed.


(** Reflection views generally work in both directions *)
Lemma special_support_for_reflect_predicates' (b c : bool) :
  b /\ c -> b && c.
Proof.
move/andP.
Show Proof.
About introT.  (** [introT] view hint gets implicitly inserted *)
exact: id.
Qed.



(** * Switching views at the goal *)

Lemma special_support_for_reflect_predicates'' (b c : bool) :
  b /\ c -> b && c.
Proof.
move=> ab.
apply/andP.  (** [apply/] syntax *)
Show Proof.  (** [introTF] view hint gets inserted *)
About introTF.
done.
Qed.



(** Specification for [eqn] -- decision procedure for equality on [nat]s *)
Lemma eqnP_my (n m : nat) : reflect (n = m) (eqn n m).
Proof.
elim: n m=> [|n IHn] [|m]; try constructor=> //.

move=> /=.

(** Need to convert a [reflect]-based propositions into biimplications *)
Search reflect -seq -"or" -"and" -"mem" -negb -minn.

Check iffP (IHn m).
(**
How the conclusion of [iffP (IHn m)] matches with the goal:

                                         reflect (n.+1 = m.+1) (eqn n m)
       (n = m -> ?Q) -> (?Q -> n = m) -> reflect ?Q            (eqn n m)

Coq infers [?Q] existential variable to be [n.+1 = m.+1]
*)
by apply: (iffP (IHn _)) => [-> | /succn_inj].

Restart.

apply: (iffP idP).   (** [idP] -- the trivial reflection view *)
- by elim: n m => [|n IHn] [|m] //= /IHn->.
- move=> ->. by elim: m.
Qed.


Lemma silly_example_iffP_andP (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
apply: (iffP idP).
Undo.
Check (iffP andP).
apply: (iffP andP).
done.
done.
Qed.


(** A better example of using [iffP] with a non-[idP] argument *)
Lemma nseqP (T : eqType) n (x y : T) :
  reflect (y = x /\ n > 0) (y \in nseq n x).
Proof.
rewrite mem_nseq andbC.
(* apply: (iffP idP); move/andP. *)
apply: (iffP andP).
(* reflect (x = y) (x == y) *)
case. move/eqP. move=>->. done.
case=>->. done.

Restart.

by rewrite mem_nseq andbC; apply: (iffP andP) => -[/eqP].
Qed.



(** * Rewriting with [reflect] predicates *)


About maxn_idPl.

Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
(* move: (leq_total n2 n1). *)
(* case. *)
(* rewrite /is_true. *)
(* Print eq. *)
(* Set Printing All. *)
(*   move/orP. case=> [le_n21 | le_n12]. *)
case/orP: (leq_total n2 n1) => [le_n21 | le_n12].

Check (@maxn_idPl n1 n2).
rewrite (@maxn_idPl n1 n2 le_n21).

(** Why does this work?
    [maxn_idPl] is _not_ a function but behaves like one here *)

Check (maxn_idPl le_n21).  (** OK, this is an ordinary equation,
                               no wonder [rewrite] works. *)

Set Printing Coercions.
Check (maxn_idPl le_n21).   (** [elimT] get implicitly inserted *)
Unset Printing Coercions.

About elimT.

(** [elimT] is a coercion from [reflect] to [Funclass],
    This means it gets inserted when one uses a reflect view as a function.
  *)

(** Essentially we invoke the following tactic: *)

Undo.
rewrite (elimT maxn_idPl le_n21).
Abort.


(** * An example of a specification for a [seq] function *)

(** [all] specification *)
About allP.
(**
    forall (T : eqType) (a : pred T) (s : seq T),
    reflect {in s, forall x : T, a x} (all a s)
*)

(** Check out some other specs in the [seq] module! *)
Search _ reflect in seq.




(*** Specs as rewrite rules *)

Example for_ltngtP m n :
  (m <= n) && (n <= m) ->
  (m == n) || (m > n) || (m + n == 0).
Proof.
by case: ltngtP.

Restart.

case: ltngtP.
done.
done.
move=>/=.
Abort.


Module Trichotomy.

Variant compare_nat m n :
   bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n true false true false false false
  | CompareNatGt of m > n : compare_nat m n false true false true false false
  | CompareNatEq of m = n : compare_nat m n true true false false true true.

Lemma ltngtP m n : compare_nat m n (m <= n) (n <= m) (m < n)
                                   (n < m)  (n == m) (m == n).
Proof.
rewrite !ltn_neqAle [_ == m]eq_sym; case: ltnP => [mn|].
  by rewrite ltnW // gtn_eqF //; constructor.
rewrite leq_eqVlt; case: ltnP; rewrite ?(orbT, orbF) => //= lt_nm eq_mn.
  by rewrite ltn_eqF //; constructor.
by rewrite eq_mn; constructor; apply/eqP.
Qed.

(** One more example *)
Lemma maxnC : commutative maxn.
Proof. by move=> m n; rewrite /maxn; case: ltngtP. Qed.

End Trichotomy.






(*** Coercions summary *)


(** * [is_true] coercion *)

(** We have already been using [is_true] coercion regularly.
    It's defined in ssrbool.v as follows:

    Coercion is_true : bool >-> Sortclass.
 *)

(** E.g. [is_true] makes the following typecheck *)
Check (erefl true) : true.



(** * [elimT] coercion *)

(**  Allow the direct application of a reflection lemma
     to a boolean assertion.

    Coercion elimT : reflect >-> Funclass.
 *)

Section ElimT_Example.

Variables b c : bool.
Hypothesis H : b || c.

Check orP H.
Set Printing Coercions.
Check orP H.
Unset Printing Coercions.

End ElimT_Example.



(** * [nat_of_bool] coercion *)

About nat_of_bool.

About leq_b1.
About mulnb.

About count_nseq.

(** You can learn more using the following search query: *)
Search _ nat_of_bool.





