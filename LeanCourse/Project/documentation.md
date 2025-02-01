# Main Goal
The goal of our project was to prove that representations of finite abelian groups are irreducible if and only if their degree is 1.
This goal is finished and can be found in `FinAbelGroupRep`.
The proof relies on representation homomorphisms, for which the required work can be found in `RepresentationHom`.
Also, we introduced basic definitions for talking about irreducibility in `InvariantSubmodules`.

# Further work
Having finished the main goal, we tried to do the future work stated in `Maschke` in Mathlib. In that file is a proof of Maschke's theorem using algebras.
Thus, we set out to connect the two notions of representations in the forms of morphisms and of algebras far enough to formulate Maschke's theorem for representations.
The required transferals of irreducibility notions are done in `IrreducibilityMeansSimpleModule`.
The new formulation of Maschke's theorem for representations uses complete reducibility and can be found in `CompleteReducibility`.
