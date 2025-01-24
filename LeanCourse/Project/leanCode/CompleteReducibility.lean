import Mathlib
import LeanCourse.Project.leanCode.InvariantSubmodules
import LeanCourse.Project.leanCode.IrreducibilityMeansSimpleModule

open Function Set Classical

noncomputable section

namespace Representation

/-
# Goal: Prove Maschke's theorem for representations using the existing algebra version

# Definitions
- `directSumRepresentation`: the natural representation given for a direct sum of *two* representations.
- `IsCompletelyReducible` predicate for representations using the `IsCompl` predicate

# todo
- resolve sorrys
- implement direct sum representations with any amount of summands
- write completely reducible representations as direct sums of irreducible sub-representations
- reformulate maschke that way

-/


-- the natural representation given for a direct sum of *two* representations
def directSumRepresentation {k G V₁ V₂: Type*}
  [CommSemiring k] [Monoid G] [AddCommMonoid V₁] [AddCommMonoid V₂] [Module k V₁] [Module k V₂]
  (ρ₁: Representation k G V₁) (ρ₂: Representation k G V₂): Representation k G (V₁ × V₂) := {
    toFun := fun g ↦ {
      toFun := fun v ↦ (ρ₁ g (LinearMap.fst k V₁ V₂ v), ρ₂ g (LinearMap.snd k V₁ V₂ v))
      map_add' := by intro x y; simp
      map_smul' := by intro m; simp
    }
    map_one' := by simp; rfl
    map_mul' := by intro g h; simp; rfl
  }


-- predicate for representations using the `IsCompl` predicate
def IsCompletelyReducible {k G V: Type*}
  [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) :=
  ∀ U : Submodule k V, IsInvariantSubmodule U ρ → ∃ U' : Submodule k V, IsInvariantSubmodule U' ρ ∧ IsCompl U U'


-- somehow convert from
-- ComplementedLattice (Submodule (MonoidAlgebra k G) V) to
-- ComplementedLattice (Submodule (MonoidAlgebra k G) ρ.asModule)
-- asModuleEquiv useful?
instance complementedLattice {k G V: Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) : ComplementedLattice (Submodule (MonoidAlgebra k G) ρ.asModule) where
  exists_isCompl := sorry


theorem ofSubmodule_ofComplIsCompl {k G V: Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U U' : Submodule (MonoidAlgebra k G) ρ.asModule) :
  IsCompl U U' → IsCompl (ofSubmodule ρ U) (ofSubmodule ρ U') := by
  intro h
  rw [isCompl_iff] at *
  obtain ⟨disUU', codisUU'⟩ := h
  constructor
  · intro W hWU hWU' w wW
    have h : ∀ x, x ∈ U → x ∈ U' → x = 0 := by
      intro x xU xU'
      have xInter : x ∈ U.carrier ∩ U'.carrier := by
        exact mem_inter xU xU'
      have xBot : x ∈ U ⊓ U' := by exact xInter
      have UU'bot : U ⊓ U' = ⊥ := by exact disjoint_iff.mp disUU'
      rw [UU'bot] at xBot
      simp at xBot
      assumption
    exact h w (hWU wW) (hWU' wW)
  · intro W hW h'W w hw
    sorry


-- maschke's theorem
theorem rep_ofFinGroup_isCompletelyReducible {k G V: Type*}
  [CommSemiring k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)] [AddCommGroup V] [Module k V]
  (ρ: Representation k G V): IsCompletelyReducible ρ := by
  intro U invU
  let UMod := (asSubmodule ρ U invU)
  obtain ⟨UMod', h⟩ := exists_isCompl UMod
  use ofSubmodule ρ UMod'
  constructor
  · exact ofSubmodule_isInvariant ρ UMod'
  · have hU : U = ofSubmodule ρ UMod := by rfl
    rw [hU]
    apply ofSubmodule_ofComplIsCompl
    exact h


theorem subReps_ofComplReducible_isComplReducible {k G V: Type*}
  [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U : Submodule k V) :
  IsCompletelyReducible ρ → IsInvariantSubmodule U ρ → IsCompletelyReducible (SubRepresentation ρ U) := by
  intro h X hX
  --obtain ⟨W, hW⟩ := h X
  sorry
