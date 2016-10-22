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

First, fetch the source code of iris:

git submodule update

*)

