From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section Classical_reasoning.

(** We assert the classical principle of double negation elimination *)
Variable DNE : forall A : Prop, ~ ~ A -> A.

(* https://en.wikipedia.org/wiki/Drinker_paradox *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x, P x -> forall y, P y.
Proof.
apply: DNE => not_DP; apply/not_DP.
exists 0=> _ y.
apply: DNE => nPy; apply/nPy.
case: not_DP.
by exists y => /nPy.
Qed.

Lemma inhabited_exists A :
  (exists x : A, True) <-> inhabited A.
Proof. by split; case. Qed.

(** Bonus: here is a bit more general formulation of the above lemma,
    we don't have to have predicates over [nat]s, having an inhabited type is enough *)
Lemma drinker_paradox' (A : Type) (P : A -> Prop) :
  inhabited A ->
  exists x, P x -> forall y, P y.
Proof.
apply: DNE => not_DP; apply/not_DP.
case=> a; exists a=> _ y.
apply: DNE => nPy; apply/nPy.
case: not_DP.
by exists y => /nPy.
Qed.

(* This closes the section, discharging over DNE *)
End Classical_reasoning.
Check drinker_paradox.



Section Misc.

Variables A B : Type.
Implicit Types x y : A * B.

Lemma prod_inj x y :
  x = y <-> (x.1, x.2) = (y.1, y.2).
Proof. by case: x; case: y. Qed.

End Misc.



Section Arithmetics.

(* an auxiliary lemma to prove min_plus_r *)
Lemma subn_leq0 n m :
  minn n m = n -> n - m = 0.
Proof.
move=> min.
(* we need injectivity of addition here *)
Search _ addn "I".
apply: (@addnI m).
rewrite -maxnE.
rewrite addn0.
rewrite -min.
Search _ maxn minn.
rewrite minKn.
by [].
Qed.

Lemma min_plus_r n m p  :
  minn n m = n -> minn n (m + p) = n.
Proof.
move/subn_leq0.
rewrite minnE.
Search _ (?n - (?m + ?p)).
rewrite subnDA.
move=> ->.
simpl.
Search _ subn 0.
rewrite sub0n.
rewrite subn0.
by [].

Restart.

(* a solution using boolean reflection which we will cover later in the course *)
move=> /minn_idPl/eqP eq0.
by rewrite minnE subnDA eq0 sub0n subn0.

(* or, alternatively *)
Restart.

move/minn_idPl => le_nm; apply/minn_idPl.
by rewrite -(addn0 n) leq_add.
Qed.

Lemma min_plus_minus m n p :
  minn n m + minn (n - m) p = minn n (m + p).
Proof.
Search _ ((?m <= ?n) || (?n <= ?m)).
move: (leq_total m n).
Search _ (_ || _) (_ \/ _).
move/Bool.orb_prop.  (* vanilla Coq, the idiomatic approach would be move/orP *)
case.
- move=> le_mn.
  rewrite minnE.
  rewrite -{1}(subnKC le_mn).
  rewrite -{2}(add0n (n-m)).
  rewrite subnDr.
  rewrite subn0.
  rewrite addn_minr.
  rewrite subnKC.
  + done.
  done.
- move/minn_idPl.
  move=> min.
  move: (min).
  move/subn_leq0.
  move=>->.
  rewrite min0n.
  rewrite addn0.
  rewrite min.
  move: min.
  by move/min_plus_r->.

Restart.

case: (leqP m n) => [le_mn | /ltnW/minn_idPl min_n].
- rewrite minnE.
  rewrite -{1}(subnKC le_mn) -{2}(add0n (n-m)) subnDr subn0.
  by rewrite addn_minr subnKC.
- move: (min_n)=> /subn_leq0 ->.
  rewrite min0n addn0 min_n.
  by rewrite min_plus_r.
Qed.

Fixpoint zero (n : nat) : nat :=
  if n is n'.+1 then zero n'
  else 0.

Lemma zero_returns_zero n :
  zero n = 0.
Proof. by elim: n. Qed.

(**
Claim: every amount of postage that is at least 12 cents can be made
       from 4-cent and 5-cent stamps. *)
(** Hint: no need to use induction here *)
Lemma stamps n : 12 <= n -> exists s4 s5, s4 * 4 + s5 * 5 = n.
Proof.
move=> /leq_div2r leq12n; exists (n %/4 - n %% 4), (n %% 4).
rewrite mulnBl -addnABC -?mulnBr ?muln1 ?leq_mul -?divn_eq //.
by rewrite (leq_trans _ (leq12n 4)) // -ltnS ltn_pmod.
Qed.

End Arithmetics.


(* ======================================== *)

(** Bonus track: properties of functions and their composition.
    Feel free to skip this part.
 *)

(** Solutions for the exercises in seminar02.v, we are going to need them later *)
Section eq_comp.
Variables A B C D : Type.

(** Note: [rewrite !compA] would fail because it keeps adding [id \o ...]
    this is due to the fact that [compA] is a convertible rule,
    so it clashes with Miller pattern unification *)
Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof. by []. Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof. by move=> f_id g12f a; move: (g12f a)=> /=; rewrite !f_id. Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof. by move=> g_id f12g a; move: (f12g a)=> /=; rewrite g_id. Qed.

End eq_comp.



(** You might want to use the lemmas from seminar02.v, section [eq_comp] *)
Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

Lemma surj_epic f : surjective f -> epic f.
Proof.
by case=> g inv_g C g1 g2 => /(eq_compr g); rewrite 2!compA => /(eq_idr inv_g).
Qed.

Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)

(** A short answer: to prove a function surjective we need to explicitly provide
    its inverse, which is not possible in general. We know nothing about type [A],
    so we cannot construct a function of type [B -> A]
    unless there is a contradictory statement in our premises,
    which is not he case here.
 *)
Abort.

End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Proof. by move=> Ef Eg D h1 h2; rewrite -2!compA => /Eg/Ef. Qed.

Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Proof. by move=> Efg D h1 h2 /(eq_compr g)/Efg. Qed.

Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Proof.
move=> Rfg.
have: surjective f by exists g.
by apply: surj_epic.
Qed.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

Lemma inj_monic f : injective f -> monic f.
Proof.
move=> f_inj A g1 g2 fg12 a.
by move: (fg12 a)=> /f_inj.
Qed.

Definition const {A B} (a : A) :=
  fun _ : B => a.

Lemma monic_inj f : monic f -> injective f.
Proof.
move=> f_mon b1 b2 fb12.
move: (f_mon B (const b1) (const b2)).
have H : f \o @const _ B b1 =1 f \o const b2 by move=> b /=; rewrite fb12.
by move/(_ H b1).
Qed.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
by move=> Mf Mg D h1 h2; rewrite 2!compA => /Mf/Mg.
Qed.

Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof. by move=> Mfg D h1 h2 /(eq_compl f)/Mfg. Qed.

Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
Proof.
move=> Sfg.
have : cancel f g by exact: Sfg.
by move/can_inj/inj_monic.
Qed.

End MonicProperties.

End PropertiesOfFunctions.
