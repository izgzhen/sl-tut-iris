(** Specification *)

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
    {{ True%I }} (let: "x" := #1 in "x")%E {{ r, (r = #1)%I }}.
  Proof.
    (* Note that the expression (or program, since heap_lang is a functional
       language) is a shallow-embedding in Coq with heavy notations involved.
       You can just try to read it as a ML-like language. *)
    iIntros "!#". (* This is the weird thing ... In Iris, hoare triple is just
    a syntactic sugar of weakest-pre style spec, which we will talk about later.
    So we need to use "!#" pattern to eliminate the always modality.
    But current context should also look reasonable to you. *)
    iIntros "_". (* Drop the useless True *)
    wp_let. (* evaluate the let expression -- which does the substitution since
               #1 is already in normal form *)
    done.
  Qed.

  (** The above expression is pretty pure, or put it another, "side-effect free".
      Let's check out a different one *)
  Example allocation:
    {{ heap_ctx }} (let: "x" := ref #1 in "x")%E {{ r, ∃ l: loc, r = #l ∗ l ↦ #1 }}.
  Proof.
    iIntros "!# #?". (* heap_ctx means we can allocate things in the heap. It is a
                      presistent assertions (duplicable but still spatial). So it is
                      introduced anonymously by pattern "#?".
                      You can also use "#HeapCtx" *)
    wp_bind (ref _)%E. (* Focus on the expression to evaluate *)
    wp_alloc l as "Hl". (* allocate ref #1 as in a cell pointed by l *)
    (* now l has *full* ownership to #1 *)
    wp_let. iExists l.
    by iSplitR "Hl".
  Qed.

(** * Weakest-pre Style *)

