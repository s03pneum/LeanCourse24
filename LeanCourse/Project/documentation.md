## Main Goal
The initial goal of our project was to prove that representations of finite abelian groups are irreducible if and only if their degree is 1.
This goal is finished and can be found in `FinAbelGroupRep.lean`.
The proof relies on representation homomorphisms, for which the required work can be found in `RepresentationHom.lean`.
Also, we introduced basic definitions for talking about irreducibility in `InvariantSubmodules.lean`.

## Further work
Having finished the main goal, we tried to do the future work stated in `Mathlib.RepresentationTheory.Maschke` in Mathlib. In that file is a proof of Maschke's theorem using the fact that every group representation corresponds to a module over the group algebra.
Thus, we set out to connect the two notions of representations in the forms of morphisms and of algebras far enough to formulate Maschke's theorem for representations.
The required transferals of irreducibility notions are done in `IrreducibilityMeansSimpleModule.lean`. The main theorem in that file states that a representation is irreducible if and only if the corresponding module over the group algebra is simple.
The new formulation of Maschke's theorem for representations uses complete reducibility and can be found in `CompleteReducibility.lean`.

## References/Sources
- The idea for the main goal came from https://leanprover-community.github.io/undergrad_todo.html 
- For the proof of the main goal, we used https://proofwiki.org/wiki/Irreducible_Representations_of_Abelian_Group
- Of course we relied on the documentation of Mathlib, mainly on https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Basic.html and https://leanprover-community.github.io/mathlib4_docs/Mathlib/RepresentationTheory/Maschke.html.
- For the contents of our formalization, we also used the contents from the seminar "Darstellungstheorie endlicher Gruppen" (S1G1) from summer 2024. This seminar was held by Prof. Dr. Jan Schröer, who wrote a script for that course. We also used that, but unfortunately it is not publicly available.
