import Mathlib
import LeanCourse.Project.leanCode.InvariantSubmodules
import LeanCourse.Project.leanCode.IrreducibilityMeansSimpleModule

universe u

open Function Set Classical

noncomputable section

namespace Representation

/-
# Goal: Prove Maschke's theorem for representations using the existing algebra version

# Definitions
- `directSumRepresentation`: the natural representation given for a direct sum of *two* representations.
- `IsCompletelyReducible` predicate for representations using the `IsCompl` predicate

# Theorems
- `ofSubmodule_ofComplIsCompl`: complements in the algebra version transfer to complements in the representation version.
- `rep_ofFinGroup_isCompletelyReducible`: this is maschke's theorem in our formulation with complete reducibility.

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


-- complements in the algebra version transfer to complements in the representation version.
-- this still contains sorrys!
theorem ofSubmodule_ofComplIsCompl {k G V: Type*} [CommSemiring k] [Group G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U U' : Submodule (MonoidAlgebra k G) ρ.asModule) :
  IsCompl U U' → IsCompl (ρ.ofSubmodule U) (ρ.ofSubmodule U') := by
  intro h
  rw [isCompl_iff] at *
  obtain ⟨disUU', codisUU'⟩ := h
  constructor
  · intro W hWU hWU' w wW
    have h : ∀ x, x ∈ U → x ∈ U' → x = 0 := by
      intro x xU xU'
      have xInter : x ∈ U.carrier ∩ U'.carrier := by exact mem_inter xU xU'
      have xBot : x ∈ U ⊓ U' := by exact xInter
      have UU'bot : U ⊓ U' = ⊥ := by exact disjoint_iff.mp disUU'
      rw [UU'bot] at xBot
      simp at xBot
      assumption
    exact h w (hWU wW) (hWU' wW)
  · intro W hW h'W w hw
    -- issue: we get (W: Submodule k ρ.asModule), so over k and not over (MonoidAlgebra k G), which should in theory just transfer
    let W' : Submodule (MonoidAlgebra k G) ρ.asModule := {
      carrier := W.carrier
      add_mem' := by
        intro a b aW bW
        exact W.add_mem aW bW
      zero_mem' := by exact W.zero_mem
      smul_mem' := by
        intro c x xW
        have h : c • x = ∑ g in c.support, c g • (ρ g x) := by
          sorry
        rw [h]
        simp at *
        refine Submodule.sum_smul_mem W _ ?_
        intro g hg
        sorry
    }
    have hW' : U ≤ W' := by exact hW
    have hW'' : U' ≤ W' := by exact h'W
    have UU'W : U ⊔ U' ≤ W' := by exact sup_le hW' hW''
    have UU'top : U ⊔ U' = ⊤ := by exact codisjoint_iff.mp codisUU'
    rw [UU'top] at UU'W
    exact UU'W hw


-- maschke's theorem
theorem rep_ofFinGroup_isCompletelyReducible {k G V: Type u}
  [Field k] [Group G] [Fintype G] [Invertible (Fintype.card G : k)]
  [AddCommGroup V] [Module k V]
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
