From iris.program_logic Require Export weakestpre hoare.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

Section spec.
  Context `{!heapG Σ}. (* Set up the heap context *)
  (** * Hoare Triples *)

  (* Hoare-triple is a classical way of expressing
     partial correctness specificatin.

Let's prove a simple triple now.
 *)

  Example let_assignment:
    {{ True%I }} (let: "x" := #1 in "x")%E {{ r, ⌜ r = #1 ⌝ }}.
  Proof.
    (* Note that the expression (or program, since heap_lang is a functional
       language) is a shallow-embedding in Coq with heavy notations involved.
       You can just try to read it as a ML-like language. *)

    iIntros "!#".
    (* This is the weird thing ... In Iris, hoare triple is just
    a syntactic sugar of weakest-pre style spec, which we will talk about later.
    So we need to use [!#] pattern to eliminate the always modality.
    But current context should also look reasonable to you. *)

    iIntros "_".
    (* Drop the useless True *)

    wp_let.
    (* evaluate the let expression -- which does the substitution since
       [#1] is already in normal form *)
    done.
  Qed.

  (** The above expression is pretty pure, or put it another, _side-effect free_.
      Let's check out a different one *)
  Example allocation:
    {{ True }} (let: "x" := ref #1 in "x")%E {{ r, ∃ l: loc, ⌜ r = #l ⌝∗ l ↦ #1 }}.
  Proof.
    iIntros "!# _".
    
    wp_bind (ref _)%E. (* Focus on the expression to evaluate *)
    wp_alloc l as "Hl". (* allocate [ref #1] as in a cell pointed by [l] *)

    (* now [l] has _full_ ownership to a heap cell containing [#1] *)

    wp_let. iExists l.
    by iSplitR "Hl".
  Qed.

  (** * Weakest-pre Style *)

  (* Why we need WP-style spec?
   
   1. It is more primitive -- Hoare triple can be encoded with WP-style spec,
      but not vice versa.
   2. Weakest preconditions are better suited for interactive proving.
      What you have in the context (including but not limited to "pre-condition")
      is displayed in the context, now your target is too prove the after the
      expression, the post-condition will hold. It is more natural than letting
      a pre-condition hanging around. *)

  Example wp_example: ∀ P: iProp Σ,
      P ⊢ WP #1 {{ _, P }}.
  Proof.
    iIntros (P) "HP".
    wp_value.
    done.
  Qed.

  (* So, how can we write WP-spec for a library function? *)
  Definition add_one : val :=
    λ: "x", "x" <- !"x" + #1.

  Lemma add_one_spec:
    ∀ (x: loc) (n: Z) (Φ: val → iProp Σ),
      x ↦ #n ∗ (x ↦ #(n + 1) -∗ Φ #())
      ⊢ WP add_one #x {{ Φ }}.
  Proof.
    iIntros (x n Φ) "(Hx & HΦ)".
    rewrite /add_one.
    wp_let. wp_load.
    wp_op. wp_store.
    by iApply "HΦ".
  Qed.

  Local Opaque add_one.

  (* The [Φ] here means any post-condition: since it is
universally qualified, we can always instantiate it with
current context in the client side, and the productions before the
wand will be introduced to the new context *)

  Lemma add_one_client: ∀ (x y: loc),
      x ↦ #1 ∗ y ↦ #2
      ⊢ WP add_one #x;; add_one #y {{ _, x ↦ #2 ∗ y ↦ #3 }}.
  Proof.
    iIntros (x y) "(Hx & Hy)".
    wp_bind (add_one _).
    iApply add_one_spec.
    iFrame "#". (* Frame out the persistent context. *)
    iFrame "Hx".
    iIntros "Hx".
    wp_seq.
    iApply add_one_spec.
    iFrame "#".
    iFrame "Hy".
    iIntros "Hy".
    iSplitL "Hx"; done.
  Qed.

  (** You can observe how the specification _generally_ fit
      in any specific client context *)

  (* TODO: Add one section about Texan triple *)
  
End spec.
