From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Section list.
  Context `{!heapG Σ}. (* Set up the heap context *)

  (** * List *)

  (** In this chapter, we are studying data-structures that
   _represent_ an abstract concept of list/list-segment.
It means that, we map the abstract list to our physical memory,
and provide a set of operations whose spec is _abstract_. *)

  (** Below is the abstract definition of list: Just using the Coq's
standard list *)

  Definition List a := list a.

  (** Compared to the imperative & low-level language, e.g. C,
heap_lang is functional & fairly high-level. It is intuitive that
we will need to use option type and pair to model the classical lisp list (since
[heap_lang] can't define ADT conveniently now:

<<
-- Haskell

data List a = Cons { hd :: a, tl :: List a }
            | Nil
>>
*)
  
  Definition nil : val := NONEV.

  Definition cons : val := λ: "x" "xl", ref SOME ("x", "xl").
  
(*
TODO: It might be clearer to draw a graph here, but I won't bother now :P
*)

  (* Here is the "shape" predicate *)
  Fixpoint isList (l: val) (xs: List val) : iProp Σ :=
    match xs with
    | [] => (l = NONEV)%I
    | x :: xs => (∃ (hd: loc) (tl: val),
                    #hd = l ∗ hd ↦ SOMEV (x, tl) ∗ isList tl xs)%I
    end.

  (** This predicate, when applied with an abstract list, maps to
its physical configuration. Now we can give spec for nil and cons.  *)

  Lemma nil_spec: True ⊢ isList nil [].
  Proof.
    simpl. rewrite /nil. auto.
  Qed.

  Lemma cons_spec (l: val) (x: val) (xl: List val) : ∀ Φ,
    heap_ctx ∗
    isList l xl ∗
    (∀ l': val, isList l' (x::xl) -∗ Φ l')
    ⊢ WP cons x l {{ Φ }}.
  Proof.
    iIntros (Φ) "(#? & Hl & HΦ)".
    rewrite /cons.
    wp_let. wp_let.
    wp_alloc l' as "Hl'".
    iApply "HΦ".
    iExists l', l.
    by iFrame.
  Qed.

  (** * List Segment *)
  
  Fixpoint isListSeg (m n: val) (xs: List val) : iProp Σ :=
    match xs with
    | [] => (m = n)%I
    | x :: xs => (∃ (hd: loc) (m': val),
                     #hd = m ∗ hd ↦ SOMEV (x, m') ∗ isListSeg m' n xs)%I
    end.

  (** we will prove a trivial lemma first *)
  Lemma list_seg_list: ∀ (xl: List val) (l: val),
      isListSeg l nil xl ⊣⊢ isList l xl.
  Proof.
    induction xl as [|x xl' IHxl']=>//.
    intros l. apply uPred.equiv_spec.
    split.
    - iIntros "Hls".
      simpl.
      iDestruct "Hls" as (hd m') "(% & Hhd & Htl)".
      subst. iExists hd, m'.
      iDestruct (IHxl' m' with "Htl") as "Hm".
      by iFrame.
    - iIntros "Hls".
      simpl.
      iDestruct "Hls" as (hd m') "(% & Hhd & Htl)".
      iExists hd, m'.
      iDestruct (IHxl' m' with "Htl") as "Hm".
      by iFrame.
      (* Look, two branches are exactly the same ! *)
  Qed.
End list.
