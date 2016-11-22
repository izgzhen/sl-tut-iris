(** * Lock *)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang proofmode notation.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.

(**

What Iris really features is its ability to reason about *concurrency*.
Actually, Iris is built to do this, and the separation logic is just part of
its arsenal.

Let's start with the CAS-lock. The source is taken from Iris library
intact, which best preserves its flavour.
*)

Definition newlock : val := λ: <>, ref #false.

(** CAS is an *atomic* operation: `CAS l old_val new_val` will atomically
compare the value at location l with old_val, if they are equal, then
l will be updated to point to the new_val.

So what try_acquire is just a wrapper of such "try" semantics of any
general lock-free operation.
*)
Definition try_acquire : val := λ: "l", CAS "l" #false #true.

(* acquire will keep trying, until it can confirm that it update
l from false to true. (and it will stay so until this thread "unlocks" it,
according to the protocol. *)
Definition acquire : val :=
  rec: "acquire" "l" := if: try_acquire "l" then #() else "acquire" "l".

Definition release : val := λ: "l", "l" <- #false.

Global Opaque newlock try_acquire acquire release.

(* From below until "proof" section is more intricate.
   What it does, simply put, is just declare what kind of
   monoid and invariants we can use. It is like, imprecisely,
   preparing some equipments before hunting the bear.

   So you can skip it for now if you are not familiar with theory behind Iris.
*)

(** The CMRA we need. *)
(* Not bundling heapG, as it may be shared with other users. *)
Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (constRF (exclR unitC))].

Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. intros [?%subG_inG _]%subG_inv. split; apply _. Qed.

Section proof.
  Context `{!heapG Σ, !lockG Σ} (N : namespace).

  (* Here is the invariant -- The KEY of proof.
     First, every thread, if it mutates some globally owned resource,
     it will interference other threads. How to specify and control this
     kind of interference is one thing that ..
   *)
  Definition lock_inv (γ : gname) (l : loc) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ #b ∗ if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: loc, heapN ⊥ N ∧ heap_ctx ∧ lk = #l ∧ inv N (lock_inv γ l R))%I.

  Definition locked (γ : gname): iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : locked γ ∗ locked γ ⊢ False.
  Proof. rewrite /locked own_valid_2. by iIntros (?). Qed.

  Global Instance lock_inv_ne n γ l : Proper (dist n ==> dist n) (lock_inv γ l).
  Proof. solve_proper. Qed.
  Global Instance is_lock_ne n l : Proper (dist n ==> dist n) (is_lock γ l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ l R : PersistentP (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma newlock_spec (R : iProp Σ):
    heapN ⊥ N →
    {{{ heap_ctx ∗ R }}} newlock #() {{{ lk γ, RET lk; is_lock γ lk R }}}.
  Proof.
    iIntros (? Φ) "[#Hh HR] HΦ". rewrite -wp_fupd /newlock /=.
    wp_seq. wp_alloc l as "Hl".
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply "HΦ". iExists l. eauto.
  Qed.

  Lemma try_acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} try_acquire lk
    {{{ b, RET #b; if b is true then locked γ ∗ R else True }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iDestruct "Hl" as (l) "(% & #? & % & #?)". subst.
    wp_rec. iInv N as ([]) "[Hl HR]" "Hclose".
    - wp_cas_fail. iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. iApply ("HΦ" $! false). done.
    - wp_cas_suc. iDestruct "HR" as "[Hγ HR]".
      iMod ("Hclose" with "[Hl]"); first (iNext; iExists true; eauto).
      iModIntro. rewrite /locked. by iApply ("HΦ" $! true with "[$Hγ $HR]").
  Qed.

  Lemma acquire_spec γ lk R :
    {{{ is_lock γ lk R }}} acquire lk {{{ RET #(); locked γ ∗ R }}}.
  Proof.
    iIntros (Φ) "#Hl HΦ". iLöb as "IH". wp_rec.
    wp_apply (try_acquire_spec with "Hl"). iIntros ([]).
    - iIntros "[Hlked HR]". wp_if. iApply "HΦ"; iFrame.
    - iIntros "_". wp_if. iApply ("IH" with "[HΦ]"). auto.
  Qed.

  Lemma release_spec γ lk R :
    {{{ is_lock γ lk R ∗ locked γ ∗ R }}} release lk {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(Hlock & Hlocked & HR) HΦ".
    iDestruct "Hlock" as (l) "(% & #? & % & #?)". subst.
    rewrite /release /=. wp_let. iInv N as (b) "[Hl _]" "Hclose".
    wp_store. iApply "HΦ". iApply "Hclose". iNext. iExists false. by iFrame.
  Qed.
End proof.

(** ACK: This source is taken from Iris library *)
