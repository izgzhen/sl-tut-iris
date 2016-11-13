(** Introduction *)

(** * Separation Logic *)

(**
Separation logic is an extension of Hoare logic. We can use it to reason about program with pointer --
or more generally, one type of value that serves as a reference to another value in memory.

Separation logic is developed by John C. Reynolds et al. at the start of this century. It is still being
studied, extended, and revised actively today.

One of the best materials for studying this topic, as far as I see, is written by Reynolds himself:

http://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2009/cs818A3-09.html

As a result, I will try to organize the "beginner chapters" of this tutorials closely around the minicourse
as shown above. This means that I assume you will read the minicourse's handouts while going over the code here,
and I will also try to implement all essential examples in this minicourse with Iris.
*)

(** * Iris *)
(**

Iris is a higher-order concurrent separation logic developed by Ralf Jung et al. in recent years.
One of the featured highlights is the simplicity of its logical foundation -- "monoids and invariants are all your need!"
Actually, even the core rules of separation logic is built on top of a small set of base rules.

Despite the infinite possibilities with Iris, we will focus on one of its instantiation -- heap-lang, a ML-like concurrent
functional language. This language is expressive enough to write the most real world algorithms, and we can shallow-embed
it inside Coq.

*)

(** * Environment Setup *)
(**

To build Iris, we need Coq 8.5pl2 and ssreflect 1.6. For more information see https://gitlab.mpi-sws.org/FP/iris-coq. But don't install Iris yet!

For first-time user, we recommend using the local version of Iris dependency. Thus, you only need to do this in the root of this repo to build everything:

    make iris-local
    make

If everything goes well, you can go through the following lines in ProofGeneral (emacs) or something other IDE.

NOTE: Because Iris uses Unicode intensively, we recommand putting this in your emacs init file: https://gist.github.com/izgzhen/010d7dedaf44eb9fe60782b6d0c8d420, if you use PG.
*)

From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export lang.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation.

(** Don't be intimidated by this large set of imports!

    Let's write a simple theorem: commutivity of separation conjunction (What is that? We will explain later).
*)

Section proof.
  Context `{!heapG Σ}. (* Set up the heap context *)

  Goal forall (P Q: iProp Σ), P ∗ Q ⊢ Q ∗ P.
  Proof.
    iIntros (P Q) "[HP HQ]".
    (**

  ...
  =========================
  ​​"HP" : P
  ​"HQ" : Q
  --------------------------------------★
  Q ★ P

    What does this context mean?

    Before ====, it is Coq context, or "pure" context.
    Between ==== and ---★, it is separation context, or "linear" context.
    And after ---★, it is separation goal.

     *)
    iSplitL "HQ"; done.
    (* Just like split ...
       but you can only have "P" in either left or right branch!
     *)
  Qed.
End proof.

