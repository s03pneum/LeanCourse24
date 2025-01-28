import Mathlib.RepresentationTheory.Basic

open Function Set Classical
noncomputable section

namespace Representation

/-
# Overview
- `IsInvariantSubsmodule` predicate for subspaces of representations
- `SubRepresentation`: the representation for a submodule
- `IsIrreducible` predicate for representations
- `degree` of a representation
- `rep_degreeOne_irreducible`: representations of degree 1 are irreducible.

-/


/-- A predicate for a submodule being invariant -/
def IsInvariantSubmodule {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (U : Submodule k V) (ρ : Representation k G V) :=
  ∀ g : G, ∀ u : U, ρ g u ∈ U

/-- this usually only makes sense for invariant submodules -/
def SubRepresentation {k G V: Type*}
  [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U : Submodule k V) :
  Representation k G U := by exact trivial k

/-- A predicate for a representation being irreducible -/
def IsIrreducible {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [Nontrivial V]
  (ρ : Representation k G V) :=
  ∀ U : Submodule k V, IsInvariantSubmodule U ρ → U = 0 ∨ U = ⊤

/-- Defines degree of a representation as rank of its module. -/
def degree {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) : Cardinal := (Module.rank k V)

/- A representation of degree 1 is irreducible. -/
theorem rep_degreeOne_irreducible {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [Nontrivial V]
  (ρ : Representation k G V) : degree ρ = 1 → IsIrreducible ρ := by
  intro h
  have hV : (Module.rank k V) = 1 := by assumption
  unfold IsIrreducible
  intro U Uinv
  have fV : FiniteDimensional k V := by exact Module.finite_of_rank_eq_one h
  have fU : FiniteDimensional k U := by exact FiniteDimensional.finiteDimensional_submodule U
  have hU : (Module.rank k U) ≤ 1 := by rw [← hV]; exact Submodule.rank_le U
  have hU' : (Module.rank k U) = 0 ∨ (Module.rank k U) = 1 := by
    rw [← Module.finrank_eq_rank'] at hU
    rw [← Module.finrank_eq_rank']
    norm_cast
    apply Nat.le_one_iff_eq_zero_or_eq_one.mp
    norm_cast at hU
  obtain hU|hU := hU'
  . left
    apply Submodule.rank_eq_zero.mp
    assumption
  . right
    rw [← Module.finrank_eq_rank'] at hU
    rw [← Module.finrank_eq_rank'] at hV
    apply Submodule.eq_top_of_finrank_eq
    rw [← hU] at hV
    norm_cast at hV
    symm
    assumption
