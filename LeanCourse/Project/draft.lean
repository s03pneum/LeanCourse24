import Mathlib
open Function Set Classical
noncomputable section

namespace Representation

/- A predicate for a subspace being irreducible -/
abbrev IsInvariantSubspace {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (U : Submodule k V) (ρ : Representation k G V) :=
  ∀ g : G, ∀ u : U, ρ g u ∈ U

/- A predicate for a representation being irreducible -/
abbrev IsIrreducible {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) :=
  ∀ U : Submodule k V, U = 0 ∨ U = V

def degree {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) : Cardinal := (Module.rank k V)

/- Definition of Homomorhpisms between Representations -/
structure RepresentationHom {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) where
  toFun : V → W
  reprStructure : ∀ g : G, ∀ v : V, toFun (ρ g v) = ψ g (toFun v)

/- A Representation of Degree One is Irreducible -/
theorem repr_degreeOne_irreducible {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) : degree ρ = 1 → IsIrreducible ρ := by
  intro h
  have hV : (Module.rank k V) = 1 := by assumption
  unfold IsIrreducible
  intro U
  have fV : FiniteDimensional k V := by exact Module.finite_of_rank_eq_one h
  have fU : FiniteDimensional k U := by exact FiniteDimensional.finiteDimensional_submodule U
  have hU : (Module.rank k U) ≤ 1 := by rw [← hV]; exact Submodule.rank_le U
  have hU' : (Module.rank k U) = 0 ∨ (Module.rank k U) = 1 := by
    sorry
  obtain hU|hU := hU'
  . left
    apply Submodule.rank_eq_zero.mp
    assumption
  . right
    rw [← Module.finrank_eq_rank'] at hU
    --apply Submodule.eq_top_of_finrank_eq

/- Representations of finite abelian groups are irreducible iff their degree is 1 -/
theorem repr_of_CommGroup_irreducible_iff_degree_one {k G V : Type*} [Field k] [IsAlgClosed k] [CommGroup G] [Finite G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) : IsIrreducible ρ ↔ degree ρ = 1 := by
  constructor
  . sorry
  . exact repr_degreeOne_irreducible ρ
