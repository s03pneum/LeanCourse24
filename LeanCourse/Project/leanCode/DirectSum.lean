import Mathlib

open Function Set Classical DirectSum
noncomputable section

namespace Representation

instance {ι k G: Type*} {β: ι → Type*}
  [CommSemiring k] [Monoid G] [∀ i, AddCommMonoid (β i)] [∀ i, Module k (β i)]
  (ρ: ι → (G →* ((β i) →ₗ[k] (β i)))):
  Representation k G (⨁ i, β i) where
  toFun := by
    intro g
    use {
      toFun := by
        intro v
        use fun i ↦ ((ρ i) g) (v i)
        sorry
      map_add' := sorry
    }
    sorry
  map_one' := sorry
  map_mul' := sorry
