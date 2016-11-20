(** Assertions *)
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

(** * Basics *)

Section basics.
  Context `{!heapG Σ}.

  (** Let's start with a very simple assertion: *)

  Variable x: loc.

  Definition foo : iProp Σ := (x ↦ #1)%I. (* %I is Iris scope, which types this expression as iProp Σ; # is used to transfrom literal to a general value *)

  (** A simple example: Assumption foo, which defines a singleton heap from x to 1,
      entails that there is a singleton heap in which x points to integer literal *)
  Example dummy: foo ⊢ ∃ n: Z, x ↦ #n.
  Proof.
    iIntros "Hfoo".
    by iExists 1.
  Qed.

  (** Note that the "entails" and "exists" are lifted from the pure logic to the Iris logic *)

  (** A more interesting lemma about commutivity of heap point-to *)

  Lemma comm_heap: ∀ (y: loc) (xv yv: val),
      x ↦ xv ∗ y ↦ yv ⊢ y ↦ yv ∗ x ↦ xv.
  Proof.
    iIntros (y xv yv) "[Hx Hy]".
    iSplitL "Hy"; done.
  Qed.

  (** About ProofMode.

As you may find by now, there are many "magical" things in proving things in Coq with Iris:

- Two Contexts: Pure (Coq) context and Spatial (Iris) context
- Specialized tactics: e.g. iExists, iIntros, iSplitL. You may infer their menaing by comparing them with the pure versions: exists, intros, and split.
- Intensive notations: These notations makes Coq scripts more readable, but sometimes, (very rarely thanks to Robbert) important things about types are
  hidden under these notations thus confusing newcomers a lot. You can use Set Printing Notations to observe this.

 In fact, this magical thing is called ProofMode, and it greatly enhances the experience of proving stuff in Iris both in terms of autamation, readability, spatial context management etc. As said in the paper[?], it makes "reasoning in the embedded logic as seamless as reasoning in the meta logic of the proof assistant".
   *)

  (** So, where is an "empty heap"? *)
  Example empty: True ∗ x ↦ #1 ⊢ x ↦ #1.
  Proof.
    iIntros "[_ Hx]". (* Note that we don't need the first conjunct -- since it is empty! *)
    done.
  Qed.

  (** But, where does a spatial proposition mean? It is something which, if used, will be consumed. Consider this: *)

  Example silly_pure: ∀ P: Prop, P → P ∧ P.
  Proof.
    intros P HP.
    split; done.
  Qed.

  (* But you can't do the same for spatial "P": *)
  Example silly_spatial: ∀ P: iProp Σ, P ⊢ P ∗ P.
  Proof.
    iIntros (P) "HP".
    iSplitL "HP". (* You can only give P to either left side or right side. *)
    - done.
    - (* stuck *) Abort.

  (* Finally, let's check out what does magic wand mean: *)
  Lemma magic_wand: ∀ p1 p2 p3: iProp Σ, (p1 ⊢ p2 -∗ p3) ↔ (p1 ∗ p2 ⊢ p3).
  Proof.
    intros p1 p2 p3.
    split.
    - intros H.
      iIntros "[HP1 HP2]".
      iApply (H with "[HP1]")=>//.
    - intros H.
      iIntros "HP1 HP2". (* note this intro pattern (for wands) is different from separating conjunction *)
      iApply H.
      iSplitL "HP1"=>//.
  Qed.

  (** Now, let's try to use disjunction *)
  Example disj_example: x ↦ #1 ⊢ x ↦ #2 ∨ x ↦ #1.
  Proof.
    iIntros "Hx".
    iRight. (* Go to right *)
    done.
  Qed.

  (** How to mix pure assertions with spatial ones ? *)
  Example mix: ∀ y: loc, (x = y) ∗ y ↦ #1 ⊢ x ↦ #1.
  Proof.
    iIntros (y) "[% Hy]". (* Use % to introduce a (unfortunately anonymous) pure assertion *)
    by subst. (* Note: by [tactic] is equal to [tactic; done.] *)
  Qed.

  (** Finally, let's prove those "derived rules" in 2.4 *)
  Lemma derived1: ∀ P Q: iProp Σ,
      Q ∗ (Q -∗ P) ⊢ P.
  Proof.
    iIntros (P Q) "[Q HQP]".
    iApply ("HQP" with "Q").
  Qed.

  Lemma derived2: ∀ R Q: iProp Σ,
      R ⊢ Q -∗ (Q ∗ R).
  Proof.
    iIntros (R Q) "HR HQ".
    by iSplitL "HQ".
  Qed.

  Lemma derived3: ∀ P Q R: iProp Σ,
      P ∗ R ⊢ P ∗ (Q -∗ (Q ∗ R)).
  Proof.
    iIntros (P Q R) "[HP HR]".
    iSplitL "HP"; first done.
    iIntros "HQ".
    iSplitL "HQ"; done.
  Qed.

  
End basics.

