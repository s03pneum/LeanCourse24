import Mathlib
open Function Set Classical
noncomputable section

/-We use the Mathlib abbreviation for representations-/
#check Representation

/-Definition of invariant subspaces (as a predicate)-/
#check Normal
def invariantSubspace (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (U : Submodule k V) (ρ : Representation k G V) :=
  ∀ g : G, ∀ u : U, (ρ g) u ∈ U

/-Definition of irreducible representations (as a predicate)-/
def irreducibleRepresentation (k G V : Type*) [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] (ρ : Representation k G V) :=
  ∀ (U : Submodule k V), invariantSubspace k G V U ρ → U = V ∨ U = 0
