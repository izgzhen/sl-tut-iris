(** Tree *)

(* Credit: Iris library.

This is a continued example of recursive data structure in Iris, following the List.
It also gives a more "useful" property and a function to specify with.

However, note that this is still not related to concurrency yet.
*)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Export tactics.
From iris.heap_lang Require Import proofmode notation.

(** An inductive definition of binary tree with integers at leaves *)
Inductive tree :=
  | leaf : Z → tree
  | node : tree → tree → tree.

(** Physical representation of a tree *)
Fixpoint is_tree `{!heapG Σ} (v : val) (t : tree) : iProp Σ :=
  match t with
  | leaf n => v = InjLV #n
  | node tl tr =>
     ∃ (ll lr : loc) (vl vr : val),
       v = InjRV (#ll,#lr) ∗ ll ↦ vl ∗ is_tree vl tl ∗ lr ↦ vr ∗ is_tree vr tr
  end%I.

(** "sum" property of the abstract tree *)
Fixpoint sum (t : tree) : Z :=
  match t with
  | leaf n => n
  | node tl tr => sum tl + sum tr
  end.

(** Program that operates on a physical tree to calculate its sum property
Note that it is a sequential computation so no synchronization or atomic
operation is needed for the accumulating operation *)

Definition sum_loop : val :=
  rec: "sum_loop" "t" "l" :=
    match: "t" with
      InjL "n" => "l" <- "n" + !"l"
    | InjR "tt" => "sum_loop" !(Fst "tt") "l" ;; "sum_loop" !(Snd "tt") "l"
    end.

Definition sum' : val := λ: "t",
  let: "l" := ref #0 in
  sum_loop "t" "l";;
  !"l".

Global Opaque sum_loop sum'.

Section proof.
  Context `{!heapG Σ}.
  Lemma sum_loop_wp v t l (n : Z) (Φ : val → iProp Σ) :
    heap_ctx ∗ l ↦ #n ∗ is_tree v t
    ∗ (l ↦ #(sum t + n) -∗ is_tree v t -∗ Φ #())
    ⊢ WP sum_loop v #l {{ Φ }}.
  Proof.
    iIntros "(#Hh & Hl & Ht & HΦ)".
    iLöb as "IH" forall (v t l n Φ). wp_rec. wp_let.
    (* Löb induction to solve recursion. Note how forall selects
       variables to generalize. *)
    destruct t as [n'|tl tr]; simpl in *.
    (* we consider two cases: t is the leaf or t is the branch *)
    - iDestruct "Ht" as "%"; subst.
      wp_match. wp_load. wp_op. wp_store.
      by iApply ("HΦ" with "Hl").
    - iDestruct "Ht" as (ll lr vl vr) "(% & Hll & Htl & Hlr & Htr)"; subst.
      wp_match. wp_proj. wp_load.
      wp_apply ("IH" with "Hl Htl"). iIntros "Hl Htl".
      wp_seq. wp_proj. wp_load.
      wp_apply ("IH" with "Hl Htr"). iIntros "Hl Htr".
      iApply ("HΦ" with "[Hl]").
      { by replace (sum tl + sum tr + n) with (sum tr + (sum tl + n)) by omega. }
      iExists ll, lr, vl, vr. by iFrame.
  Qed.

  Lemma sum_wp v t Φ :
    heap_ctx ∗ is_tree v t ∗ (is_tree v t -∗ Φ #(sum t))
    ⊢ WP sum' v {{ Φ }}.
  Proof.
    iIntros "(#Hh & Ht & HΦ)". rewrite /sum' /=.
    wp_let. wp_alloc l as "Hl". wp_let.
    wp_apply (sum_loop_wp with "[- $Hh $Ht $Hl]").
    rewrite Z.add_0_r.
    iIntros "Hl Ht". wp_seq. wp_load. by iApply "HΦ".
  Qed.
End proof.
