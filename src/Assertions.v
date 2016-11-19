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
  
End basics.

