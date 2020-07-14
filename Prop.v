Require Import String.
Require Import DProp.Tactics.
Require Import List.
Import List.ListNotations.

(** * Syntax *)
Inductive sentence : Set :=
| p_top : sentence
| p_var : nat -> sentence
| p_conj : sentence -> sentence -> sentence
| p_neg : sentence -> sentence.

(** We ask Coq to infer that equality of sentences is decidable *)
Scheme Equality for sentence.
Check sentence_eq_dec. (* : : forall x y : sentence, {x = y} + {x <> y} *)

(** We'll give names to a few of the variables for convenience... *)
(* Notation "[ n ]" := (p_var n). *)
Notation "'P'" := (p_var 0).
Notation "'Q'" := (p_var 1).
Notation "'R'" := (p_var 2).

(** ... and set up some pleasant notations. Notice some of these
    notations define new connectives, like disjunction, in terms of
    simpler ones.

    These notations use Unicode. Proof General and CoqIDE both support
    quick Unicode entry by typing TeX-like strings, see


   - #<a href="https://coq.github.io/doc/master/refman/practical-tools/coqide.html">Coqide information</a> (See "Using Unicode symbols")# *)
(**
   - #<a href="https://github.com/cpitclaudel/company-coq">Company Coq</a>#

*)
Notation "⊤" := (p_top). (* \top *)
Notation "x ∧ y" := (p_conj x y) (at level 50). (* \land or \wedge *)
Notation "¬ x" := (p_neg x) (at level 10). (* \neg *)
Notation "⊥" := (¬ ⊤). (* \bot *)
Notation "x ∨ y" := (¬ (¬ x ∧ ¬ y)) (at level 50). (* \lor or \vee *)
Notation "x ⇒ y" := (¬ x ∨ y) (at level 70). (* \Rightarrow *)


(** Next we define the semantics of our language. We want to translate
    sentences into Coq-level propositions, i.e. elements of type
    [Prop]. You might expect to use [bool] here instead. Both choices
    "work," but using [Prop] is more general and more natural for the
    metatheory we build here today, and ultimately it better captures
    the idea that a semantics maps object-level propositions into
    host-level propositions. Further information about this topic is
    provided below.  *)

(** A valuation might also be called an _interpretation_ or a _model_,
    especially in the context of higher-order logics.

    Notice that we require a valuation to come with a proof that the
    propositional symbols of our language are mapped to propositions
    for which the excluded middle is provable (or taken as an
    axiom). This is necessary for our logic to be sound, which is
    discussed in the section on proof theory.

*)
Class valuation : Type :=
  { val : nat -> Prop
  ; excluded_middle : forall n, val n \/ ~ (val n)
  }.

(** This coercion tells Coq that we can use a [valuation] as a
    function [nat -> Prop] by using its [val] field, for convenience. *)
Coercion val : valuation >-> Funclass.

(** * Model theory *)

(** We define a recursive function, [denotation], which translates
    sentences to "actual" propositions, meaning types whose sort is [Prop].

    Another good name for this function could be "is_true" or "translation."
    Notice that any valuation [v] defines a subset [denotation v] of sentences,
    namely the "true" ones.
*)
Fixpoint denotation (v : valuation) (s : sentence) : Prop :=
  match s with
  | p_top => True
  | p_var x => val x
  | p_conj s1 s2 => denotation v s1 /\ denotation v s2
  | p_neg s1 => not (denotation v s1)
  end.

(** Hereafter we let [denotation] take the valuation as an implicit
    argument. This follows common mathematical practice in which one
    generally assumes some valuation is clear from the context.
*)
Arguments denotation {v} s.

Notation "⟦ ϕ ⟧" := (denotation ϕ). (* \llbracket and \rrbracket *)

(** The law of excluded middle extends to the entire language straightforwardly. *)
Lemma full_lem : forall {v : valuation}, forall ϕ, ⟦ ϕ ⟧ \/ ⟦ ¬ ϕ ⟧.
Proof.
  intros v ϕ. induction ϕ.
  - simpl. intuition.
  - exact (excluded_middle n).
  - simpl. intuition.
  - simpl. intuition.
Qed.

(** This tactic splits a (Coq-level) proof into two cases: one in
    which ϕ is true and one in which it is false. *)
Ltac lem ϕ := destruct (full_lem ϕ).

(** Sample usage of the [lem] tactic. *)
Goal forall ϕ, forall v : valuation, ⟦ ϕ ⟧ \/ ⟦ ¬ ϕ ⟧.
Proof.
  intros.
  lem ϕ.
  - left. auto.
  - right. auto.
Qed.

(** In this file, we're not very interested in individual valuations. Instead,
    we would like to define a notion of "truth" which abstracts over the valuation,
    capturing the idea that a sentence is true under every possible interpretation.
*)
Definition tautology (ϕ : sentence) := forall v : valuation, ⟦ ϕ ⟧.

(** The universal quantifier---the dependent product---can be thought
    of as a kind of infinite conjunction asserting the truth of ϕ
    under _every_ interpretation. *)

(** But we aren't just interested in tautologies. Often we want to
    restrict our attention to only those valuations which make certain
    pre-chosen sentences true. We develop this idea now.  *)

(** A set of sentences is _satisfied_ or _modeled_ by a valuation if
    all of its elements are true under that valuation. Elements of [Γ]
    may also be called "axioms." *)
Definition models (v : valuation) (Γ : list sentence) : Prop :=
  forall ϕ, List.In ϕ Γ -> ⟦ ϕ ⟧.

(** A valuation that models Γ is called a model, unsurprisingly. *)
Definition model Γ := { v : valuation | models v Γ }.

(** A set of axioms _entails_ a sentence when that sentence is true
    under all valuations that also satisfy the axioms, i.e. all
    models. This relation also known as _semantic consequence_ or
    _logical consequence_.

    We might also read this definition as a restricted variant of
    [tautology] that intersects only over that subset of valuations
    which satisfy Γ. This property is sometimes known as being /valid/
    for Γ (but this word is sometimes used differently). When we
    formalize our proof system, the most ideal outcome is that the
    provable formulas are precisely the valid ones. *)
Definition entails (Γ : list sentence) (ϕ : sentence) :=
  forall v, models v Γ -> ⟦ ϕ ⟧.

Notation "Γ ⊧ ϕ" := (entails Γ ϕ) (at level 70).

Hint Unfold tautology : dp.
Hint Unfold models : dp.
Hint Unfold entails : dp.

(** Use the following tactic to quickly get rid unfold many definitions. *)
Tactic Notation "unf" := (repeat autounfold with dp in *).


(** Exercise 1 (easy): Prove that a sentence is a tautology if and
    only if it is entailed by the empty set of axioms.

    Note: This is almost true by definition, but formalizing logics in
   Coq often means proving such "obvious" facts. *)
Theorem exercise1 : forall ϕ, tautology ϕ <-> nil ⊧ ϕ.
Proof.
Admitted.

(** Exercise 2 (easy): Prove the following tautology.

 *)
Theorem exercise2 : forall ϕ : sentence, tautology (ϕ ∨ ¬ ϕ).
Proof.
Admitted.

(** Exercise 3 (medium): Have we formalized implication correctly?
    Check our work by proving if [x ⇒ y] is true and [x] is true, then
    [y] is true.

    Hint: Use the [lem] tactic to do case analysis on [Q]. You may
    want to [Unset Printing Notations]. *)
Theorem exercise3 : forall (v : valuation), ⟦ P ⇒ Q ⟧ /\ ⟦ P ⟧ -> ⟦ Q ⟧.
Proof.
Admitted.

(** Logically equivalent formulas are those which have the same
    denotation under every interpretation. Since we are interpreting
    into [Prop], rather than [bool], we define this notion using
    biconditionality (at the Coq level) rather than equality of
    boolean values, but the idea is the same. *)
Definition equivalent ϕ ψ := forall (v : valuation), ⟦ ϕ ⟧ <-> ⟦ ψ ⟧.

  (** Exercise 4 (easy): Prove that [P] and [P ∧ ⊤] are semantically
  equivalent.  *)
Theorem exercise4 : equivalent P (P ∧ ⊤).
Proof.
Admitted.

 (** Exercise [5] (medium): Prove that [P] and [P ∨ ¬ ⊤] are
     semantically equivalent.  Use [lem P]. *)
Theorem exercise5 : equivalent P (P ∨ ¬ ⊤).
Proof.
Admitted.

 (** Exercise 6 (hard): Why did the last exercise require law of
     excluded middle, when Coq trivially proves the following
     intuitionistic tautology? Can you prove (with pen and paper, not
     in Coq) that the last exercise cannot be completed without LEM?
     *)
Goal forall p : Prop, p <-> (p \/ ~ True).
  tauto.
Qed.

(** * Proof theory

    This section explores basic proof theory. The goal is to define a
    particular syntactical notion called "proof," where each proof is
    associated with a formula called its "conclusion." Formulas with
    proofs are "theorems." Later, our primary goal will be to show
    that a formula ϕ is entailed by Γ precisely if there is a proof
    with conclusion ϕ using only axioms from Γ, i.e. the theorems are
    exactly the valid statements. (Many logics do not have this strong
    property, but propositional logic does.)  *)

(** The following proof system is a natural deduction, which is
    essentially the type system of the simply typed lambda
    calculus. However, we are not formalizing lambda terms here, only
    the type inhabitation property itself. To be precise, you might
    call this a version of natural deduction with localized
    hypotheses, but without proof objects.

    The distinguishing feature of natural deduction is that each
    logical connective is defined by introduction and elimination
    rules. Another common system is a "sequent calculus," which looks
    visually similar but is subtly different. A sequent calculus would
    better highlight the symmetries of logic and lend itself better to
    automated proof search and inversion lemmas (discussed briefly in
    the section on incompleteness). *)

Reserved Notation "Γ ⊢ ϕ" (at level 90).
Inductive provable (Γ : list sentence) : sentence -> Prop :=
| j_var : forall ϕ, List.In ϕ Γ -> Γ ⊢ ϕ
| j_conj_intro : forall ϕ ψ, Γ ⊢ ϕ -> Γ ⊢ ψ -> Γ ⊢ ϕ ∧ ψ
| j_conj_elim1 : forall ϕ ψ, Γ ⊢ ϕ ∧ ψ -> Γ ⊢ ϕ
| j_conj_elim2 : forall ϕ ψ, Γ ⊢ ϕ ∧ ψ -> Γ ⊢ ψ
| j_neg_intro : forall ϕ, ϕ :: Γ ⊢ ⊥ -> Γ ⊢ ¬ ϕ
| j_neg_elim : forall ϕ ψ, Γ ⊢ ϕ -> Γ ⊢ ¬ ϕ -> Γ ⊢ ψ
| j_raa: forall ϕ, (¬ ϕ :: Γ ⊢ ¬ ⊤) -> Γ ⊢ ϕ
| j_top_intro : Γ ⊢ ⊤
where "Γ ⊢ ϕ" := (provable Γ ϕ).

(** The next two lemmas are fundamental properties of most logics.
    Substitution shows that provable hypotheses are
    redundant. Weakening says unused hypotheses are okay and plays an
    important role in proving substitution. *)
Lemma weakening : forall Γ1 Γ2 Γ3 ϕ,
    Γ1 ++ Γ2 ⊢ ϕ ->
    Γ1 ++ Γ3 ++ Γ2 ⊢ ϕ.
Proof.
  intros ? ? ? ? Hϕ.
  remember (Γ1 ++ Γ2) as Γ.
  generalize dependent Γ1.
  induction Hϕ; intros; subst.
  - apply j_var.
    rewrite ?List.in_app_iff in *.
    intuition.
  - apply j_conj_intro; auto.
  - eapply j_conj_elim1. eauto.
  - eapply j_conj_elim2. eauto.
  - eapply j_neg_intro.
    specialize (IHHϕ (ϕ :: Γ1)). simpl in *. auto.
  - eapply j_neg_elim. eapply IHHϕ1; reflexivity. auto.
  - eapply j_raa. specialize (IHHϕ (¬ ϕ :: Γ1)).
    simpl in *. eauto.
  - apply j_top_intro.
Qed.

(** To picture substitution, imagine a natural deduction derivation D
    that uses of ψ using hypotheses from Γ1, Γ2, and ϕ. Given a
    natural deduction derivation E of ϕ, picture "moving up" the tree
    of D and finding all leaves that introduce the axiom ϕ, and
    replace them with E. Through Curry-Howard, this is essentially
    function evaluation. *)
Lemma substitution : forall Γ1 ϕ Γ2 ψ,
    Γ1 ++ (ϕ :: Γ2) ⊢ ψ ->
    Γ2 ⊢ ϕ ->
    Γ1 ++ Γ2 ⊢ ψ.
Proof.
  intros ? ? ? ? J1 J2.
  remember (List.app Γ1 (ϕ :: Γ2)).
  generalize dependent Γ1.
  induction J1; intros Γ1 Eq; subst.
  - destruct (sentence_eq_dec ϕ ϕ0).
    { (* Equal *)
      subst.
      replace (Γ1 ++ Γ2) with (nil ++ Γ1 ++ Γ2) by (rewrite app_nil_l; auto).
      apply weakening. rewrite app_nil_l. auto. }
    { (* Unequal *)
      apply j_var.
      rewrite ?List.in_app_iff in *.
      destruct H; try tauto.
      inversion H; subst. contradiction. tauto. }
  - apply j_conj_intro; auto.
  - eapply j_conj_elim1; auto.
  - eapply j_conj_elim2; auto.
  - apply j_neg_intro. specialize (IHJ1 (ϕ0 :: Γ1)). simpl in *. eauto.
  - apply j_neg_elim with (ϕ := ϕ0); auto.
  - apply j_raa.
    specialize (IHJ1 (¬ ϕ0 :: Γ1)). simpl in *. eauto.
  - apply j_top_intro.
Qed.

(** * Relating proofs to truths*)

(** The following exercise is mostly straightforward but
    requires a good grasp on the definitions in play. By unfolding the
    definitions, we see that soundness is a computation with two inputs:
    - a "proofs" of a "proposition"
    - a model of the axioms Γ
    and the output is exactly a (Coq-level) proof of the (Coq-level) proposition
    which interprets the "proposition" in that model!
 *)

(** Exercise 7 (medium/hard): Prove that all sentences provable from Γ
    are logically entailed by Γ.

    The negation introduction and reductio ad absurdum cases may
    require some pen-and-paper thinking. You will certainly need to
    use the [lem] tactic at some point. *)
Theorem soundness : forall Γ ϕ, (Γ ⊢ ϕ) -> Γ ⊧ ϕ.
Proof.
Admitted.


(** Our next theorem is the converse of soundness, known as semantic
    completeness. It states that logically valid sentences have
    proofs. There is another notion of completeness ("syntactical
    (in)completeness") discussed later. It is sometimes clear from
    context which notion of completeness one has in mind, since
    well-known logics have equally well-known completeness properties,
    but this can also be a source of confusion to newcomers. The
    reader is advised to be very careful when reading discussions of
    this topic on the internet, which are frequently confusing and
    often simply incorrect.

    Many logics do not have semantic completeness. Fortunately,
    propositional logic is one of the logics with this
    property. Unfortunately, proving this is difficult, even for such
    a simple system. In fact, that we won't even try to prove it in
    Coq. You are encouraged to attempt it to find where the difficulty
    lies.

    Why should this be hard to prove? Consider the premise: In all
    valuations satisfying every sentence of Γ, ϕ is true. This quite
    abstract condition is a statement about truth tables. If we read
    the statement of completeness as the type of a constructive proof
    in Coq, we find a challenging problem: "Given the fact that all
    rows of a truth table that happen to satisfy each formula in Γ
    also satisfy ϕ, find a natural deduction derivation of ϕ."

    Notice the premise gives us almost no information about ϕ, not
    even its basic structure. The sentences of Γ may also be very
    complex, perhaps more complex than ϕ, so they don't necessary tell
    us anything about ϕ's subformulas. In fact, while ϕ may be true
    under every Γ-satisfying valuation, each Γ-satisfying row of the
    truth table might make ϕ true "for different reasons," so to speak
    (try some examples). Where do we get started?

    Nonetheless, this theorem is true, and can even be proved
    constructively. For now, we admit it without proof.  *)
Theorem completeness :  forall Γ ϕ, Γ ⊧ ϕ -> Γ ⊢ ϕ.
Proof.
  intros Γ ϕ.
  intros mod.
  unf.
  (* ????????????????????????????? *)
Admitted.

  (** Exercise 8 (easy? hard?): Attempt to prove the following: "There
  is a sentence of propositional logic that is neither provable nor
  disprovable from the empty set of axioms."

  Use the formula [P] (a simple propositional variable) as ϕ.  Attempt
  to prove this by induction on the derivation of P. A template has been provided.
  What happens?
 *)
Theorem syntactical_incompleteness : exists ϕ, not (nil ⊢ ϕ) /\ not (nil ⊢ ¬ ϕ).
Proof.
  exists P.
  split; intro J.
  - Case "P is not provable".
  (** We want to scrutinize the supposed derivation of [P].
      If we just do [induction J], Coq will automatically generalize over the context and conclusion P,
      as if were trying to show there are no proofs of anything. To avoid this silly behavior,
      we tell Coq to remember both the conclusion P and the emptiness of the context.
      We also discharge trivial cases instantly. *)
    Ltac cleanup := repeat match goal with | H : _ |- _ => specialize (H eq_refl) end.
    remember nil as empty; remember P as conc;
      induction J; subst; cleanup.
    + SCase "j_var".
      (* for you to finish *)
      admit.
    + SCase "j_conj_intro".
      (* contradiction, the conclusions don't match *)
      inversion Heqconc.
    + SCase "j_conj_elim1".
      (* Why doesn't the induction hypothesis apply?
         What happens if you try [inversion] on the [J]? Why?
       *)
      admit.
    + SCase "j_conj_elim2".
      (* Same story as above. *)
      admit.
    + SCase "j_neg_intro".
      (* contradiction, the conclusions don't match *)
      inversion Heqconc.
    + SCase "j_neg_elim".
      (* Why doesn't the induction hypothesis apply?
         What happens if you try [inversion] on the [J]? Why?
       *)
      admit.
    + SCase "j_raa".
      (* Why doesn't the induction hypothesis apply?
         What happens if you try [inversion] on the [J]? Why?
       *)
      admit.
    + SCase "j_top_intro".
      (* contradiction, the conclusions don't match *)
      inversion Heqconc.
  - Case "~ P is not provable".
    remember nil as empty; remember (¬ P) as conc;
    induction J; subst; cleanup.
    + SCase "j_var".
      (* for you to finish *)
      admit.
    + SCase "j_conj_intro".
      (* contradiction, the conclusions don't match *)
      inversion Heqconc.
    + SCase "j_conj_elim1".
      (* What happens if you try [inversion] on the [J]? Why?
       *)
      admit.
    + SCase "j_conj_elim2".
      (* Same story as above. *)
      admit.
    + SCase "j_neg_intro".
      inversion Heqconc. subst; clear Heqconc.
      (* What happens if you try [inversion] on the [J]? Why? *)
      admit.
    + SCase "j_neg_elim".
      (* What happens if you try [inversion] on the [J]? Why?
       *)
      admit.
    + SCase "j_raa".
      (* What happens if you try [inversion] on the [J]? Why?
       *)
      admit.
    + SCase "j_top_intro".
      (* contradiction, the conclusions don't match *)
      inversion Heqconc.
Abort.

(** Exercise 9 (easy):
    What do the hard cases above have in common? (Hint: Look at the
    names of the rules that caused us difficulty.).
*)

(** The theorem above seems obvious, but it is hard to show by
    examining proof trees. The trouble is that in each elimination
    rule, we cannot be confident that the rule used to prove the
    hypothesis is a corresponding induction rule. Indeed, it might not
    be: Perhaps we prove [P] by proving [P /\ Q], and perhaps to prove
    /that/ we use reductio ad absurdum (for example). Can you
    rule this out?

    Although implication is not defined primitively, it is an
    illustrative example: Perhaps we prove [P] by showing [Q ⇒ P] and
    [Q]. How can we rule this out? Fundamentally we need a
    _cut-elimination_ theorem, specifically the corollary of a
    canonical form lemma (or inversion lemma). This would justify a
    more controlled case analysis by showing, without loss of
    generality, that we may assume proofs are of a particularly simple
    form.

    We won't prove this hard theorem here. Instead, we can show the
    above theorem by using soundness: We cannot prove [P] because it
    is not true in all models!  *)

Definition vtrue : valuation :=
  {| val := fun n => True ; excluded_middle := ltac:(intuition) |}.

Definition vfalse : valuation :=
  {| val := fun n => False ; excluded_middle := ltac:(intuition) |}.

(** Exercise 10 (medium): Prove the following statement using
    the two constant valuations defined above. *)
Theorem syntactical_incompleteness : exists ϕ, not (nil ⊢ ϕ) /\ not (nil ⊢ ¬ ϕ).
Proof.
Admitted.


(** * Commentary *)

(** ** Understanding Incompleteness

    So how can we understand Gödel's incompleteness theorem?

    Let's imagine starting over at the beginning. Suppose instead of
    formalizing propositional logic, we allowed propositions to vary
    over tuples of /terms/, as well as introducing quantifiers. This
    would be first-order logic (FOL).

    Formalizing the syntax is not particularly hard (albeit
    tedious). The semantics are also straightforward: The valuation
    primarily consists of a type [D] called the /domain/, with
    constants mapped to terms of [D], and functions denoting Coq-level
    functions over D. Finally, relations will denote subsets of D
    (e.g., binary relations are of type [D -> D -> Prop].

    The proof rules are also not too complicated: To prove a
    universally quantified sentence, give a natural deduction proof of
    the body after substitution by a fresh variable known as a
    /parameter/. Existentials are proved by proving the body for an
    arbitrary closed term.

    It turns out, this logic is also complete: if ϕ is true in all
    models satisfying Γ, there is a natural deduction proof of ϕ using
    the set Γ as axioms. This is Gödel's completeness theorem. First
    order logic is essentially the strongest logic that can have this
    property, as provability (as a semi-decidable property) is too
    weak to properly capture the semantics of higher logics.

    Finally, instead of considering an arbitrary Γ, consider a
    particular set of sentences called the /Peano axioms/. (This set
    is actually infinite due to the induction schema, so we would need
    to tweak our definitions to handle this.) This combination of
    first-order logic with a fixed set Γ of Peano axioms is
    first-order Peano arithmetic. Coq's natural numbers type [nat] is a
    model of this theory, but one can show there are other models.  *)
    (** Gödel proved the following fact (actually, Gödel's theorem is
    significantly more general. But the following is a corollary.):
    There is a sentence ϕ of the language which is: *)
(**
    - True, in the sense that it is true when interpreted into the model given by
      [nat].
    - Unprovable: There is no natural deduction derivation of
      this sentence.

    Since Gödel also proved first-order logic is complete, as an
    instant corollary we see ϕ is:
    - invalid: There are models in Coq of first-order Peano
      arithmetic in which the sentence is not true.
    *)
(** This last fact is somewhat of a coincidence. Gödel's
    incompleteness theorem applies equally to say, second-order
    arithmetic. That theory also has a (different!) sentence which is
    true when interpreted into Coq's [nat] type, but unprovable in this
    theory. However, this sentence is valid because second order
    arithmetic has only one model, [nat], in which the sentence is true.
    *)

(** ** Why is incompleteness important? Or is it?

    Clearly, syntactical incompleteness is not generally
    surprising. For instance

     - Coq is incomplete because it neither
       proves nor disproves LEM
     - Group theory is incomplete because it
       neither proves nor disproves the commutativity property
     - Propositional logic is incomplete because it neither proves nor
       disproves any atomic propositional symbol P *)

(** It is somewhat surprising that Peano arithmetic is incomplete,
       because it is not at all obvious which properties of [nat] are
       being left out. What else can we add? But it's still not
       terribly hard to understand, either.  *)

(** But Gödel's theorem says a lot more than this, because the real
    theorem proves that **any** theory of natural numbers is
    incomplete, provided: *)
(**
   - we can recognize valid proofs when we see them
   - the theory can prove basic facts (things which can be proved without
     even using induction) *)
(** Surely it is reasonable to say Gödel's theorem proves the
    incompleteness of any reasonable number theory. It is the
    _fundamental inability to ever form a complete number theory_
    which is so surprising.

    Furthermore, some additional logic from Gödel proves that such a theory
    cannot prove its own consistency. But why do we care? After all,
    if we don't trust a logic, then we would never trust such a proof
    of consistency in the first place. The answer is simple: Because
    if arithmetic can't prove the consistency of itself, obviously it
    could never prove the consistency of all of mathematics! This
    effectively invalidates Hilbert's program to "finitize" mathematics. *)

(** ** Does this mean natural numbers can't be defined?

    Not in any mathematical sense. Coq can prove the uniqueness of [nat]
    with some ease. ZFC (set theory) can also prove that there is a
    set, omega, with the properties of natural numbers which is unique
    up to ordinal isomorphism. If we upgrade first-order Peano
    arithmetic to its second-order version, both Coq and ZFC (etc.)
    prove that there is exactly one type/set that can model this
    theory, so the valid first-order statements of second-order Peano
    arithmeitic are precisely the "true" facts about natural numbers
    (that are definable in first-order logic). Unfortunately, this
    instantly proves second-order logic lacks the completeness
    property of first-order logic, since the provable sentences of
    second-order P.A. must be a strict subset of the true ones.

    And so provided you are willing to work within a powerful theory
    like Coq, there is absolutely a unique "thing" called the natural
    numbers. It just happens that there will be some sentence of our
    logic that we cannot prove, even though it is true if you
    interpret your metalogic as a formal theory (inside some other
    theory).  *)

(** ** Interpreting into Prop and bool

    You might expect that we would translate propositional logic into
    [bool] instead. This would work for most purposes, and might better
    align with your normal intuition for propositional logic, but
    there are several reasons to prefer translation into [Prop] over [bool]:
 *)
(**
    1.) Due to Coq's constructive nature, we can only write functions
    of type [sentence -> bool] that we can compute. This means we can only
    describe computable models in Coq, which rules out much of
    mathematics if you extend this to higher-order logics. In the best
    case scenario, this is just an artificial limitation on which
    individual models we can define in Coq. In some scenarios, it
    might limit what we can prove about the metatheory, since we can't
    describe uncomputable counterexamples, for example.
 *)
(**
    2.) Ultimately a semantics **must** map object-level propositions
    into meta-level propositions, since [ X ⊧ ϕ ] is a proposition in
    the host logic--that's the whole point. If we used a boolean
    valued semantics in Coq, the notion [X ⊧ ϕ] must be understood as
    the Coq-level proposition [⟦ ϕ ⟧ = 1] (for valuations satisfying
    [X]), which means our boolean-semantics must be composed with the
    function [fun b : bool => b = true : bool -> Prop]. Again, this "works," but it
    is somewhat awkward for some purposes in Coq.

    A [bool]-valued semantics might be preferred if we want to compute
    with propositional logic (such as to model circuits), but our
    perspective is that [Prop]-valued interpretations are the more
    general approach, and more illuminating when understanding the
    relationship between the host and guest logics. This approach is
    called algebraic semantics, and with propositional logic it means
    our valuatons can be any Boolean-algebra homomorphism. Using [bool]
    is then a kind of degenerate case.

    How is our approach more general? Consider that ⟦ p → p ⟧ is a
    propositional tautology, and accordingly [⟦ p ⟧ → ⟦ p ⟧] is
    provable in Coq no matter what [ Prop ] we assign to [p], even if
    that proposition is not itself provable in Coq. This illustrates
    that the soundness of propositional logic does not depend on the
    fact that we often study computable models of this logic.

    However, there are some caveats to the algebraic approach in Coq:

    1. We must assume LEM, or at least assume (or prove) this property
    for every valuation we consider in order to have soundness. This
    is a result of interpreting propositional logic into a
    constructive logic.

    2. If we want to "count" valuations (common when thinking about
    circuits), the right notion of equivalence between two valuations
    is that two interpretations yield equi-provable sentences in
    Coq. Different valuations are rarely literally equal.

*)
