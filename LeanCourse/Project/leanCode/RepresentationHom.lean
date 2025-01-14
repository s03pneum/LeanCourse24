import LeanCourse.Project.leanCode.InvariantSubmodules
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Order.CompletePartialOrder

open Function Set Classical
noncomputable section

namespace Representation

/-
# Overview

- `RepresentationHom` class
- instances of `RepresentationHom`
  - coercions of RepresentationHom to LinearMap and Function
  - `zeroRepHom`: The zero map is a repHom.
  - `rep_yields_repHom_commMonoid`: Any element of the monoid acts as a repHom.

- `repHom_image_isInvariantSubmodule`: The image of a repHom is an invariant subspace.
- `repHom_kernel_isInvariantSubmodule`: The kernel of a repHom is an invariant subspace.

- `repHom_betweenIrreducibles_isZeroOrIso`: RepHoms between irreducible representations are zero or isomorphisms.
- `endomorphism_irreducibleRep_scalar`:
  Endomorphisms of irreducible representations over algebraically closed fields are given by multiplication with a scalar.

-/


/-- Definition of homomorhpisms between representations -/
@[ext] class RepresentationHom {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) extends LinearMap (RingHom.id k) V W where
  reprStructure : ∀ g : G, ∀ v : V, toLinearMap (ρ g v) = ψ g (toLinearMap v)

/-- Coercion of RepresentationHom to LinearMap -/
instance {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  {ρ : Representation k G V} {ψ : Representation k G W} : CoeFun (RepresentationHom ρ ψ) (fun _ ↦ V →ₗ[k] W) where
  coe := by
    intro θ
    use ⟨θ.toFun, ?_⟩
    simp; intro x y; simp

/-- Coercion of RepresentationHom to Function -/
instance {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  {ρ : Representation k G V} {ψ : Representation k G W} : CoeFun (RepresentationHom ρ ψ) (fun _ ↦ V → W) where
  coe := by intro rh; use rh.toFun

/-- The zero linear map is a repHom. -/
instance zeroRepHom {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) : (RepresentationHom ρ ψ) where
  toFun := fun v ↦ 0
  map_add' := by intro x y; simp
  map_smul' := by intro m x; simp
  reprStructure := by intro h v; simp

/-- For a given representation, any element of the monoid yields a repHom on the representation itself. -/
instance rep_yields_repHom_commMonoid {k G V : Type*} [CommSemiring k] [CommMonoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (g : G) : (RepresentationHom ρ ρ) where
  toFun := ρ g
  map_add' := by intro x y; simp
  map_smul' := by intro m x; simp
  reprStructure := by {
    intro h v
    simp
    calc
      (ρ g) ((ρ h) v) = ((ρ g) * (ρ h)) v := by rfl
                    _ = (ρ (g*h)) (v)     := by refine LinearMap.congr_fun ?h v; exact Eq.symm (MonoidHom.map_mul ρ g h)
                    _ = (ρ (h*g)) (v)     := by apply LinearMap.congr_fun; apply congr_arg; exact CommMonoid.mul_comm g h
                    _ = ((ρ h) * (ρ g)) v := by apply LinearMap.congr_fun; exact MonoidHom.map_mul ρ h g
                    _ = (ρ h) ((ρ g) v)   := by rfl
  }

/- The image of a repHom is an invariant submodule. -/
theorem repHom_image_isInvariantSubmodule {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) (θ : (RepresentationHom ρ ψ)) :
  IsInvariantSubmodule (LinearMap.range θ.toLinearMap) ψ := by
  simp [IsInvariantSubmodule]
  intro g v
  use (ρ g) v
  exact θ.reprStructure g v

/- The kernel of a repHom is an invariant submodule. -/
theorem repHom_kernel_isInvariantSubmodule {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) (θ : (RepresentationHom ρ ψ)) :
  IsInvariantSubmodule (LinearMap.ker θ.toLinearMap) ρ := by
  simp [IsInvariantSubmodule]
  intro g v vinker
  calc
    θ ((ρ g) v) = ψ g (θ.toLinearMap v) := by exact θ.reprStructure g v
              _ = ψ g 0                 := by rw [vinker]
              _ = 0                     := by exact LinearMap.map_zero (ψ g)

/- RepHoms between irreducible representations are zero or isomorphisms -/
theorem repHom_betweenIrreducibles_isZeroOrIso {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Nontrivial V] [Nontrivial W]
  (ρ : Representation k G V) (ψ : Representation k G W) (θ : (RepresentationHom ρ ψ)) :
  IsIrreducible ρ → IsIrreducible ψ →  θ = zeroRepHom ρ ψ ∨ Bijective θ := by {
  intro hρ hψ
  have hker : (LinearMap.ker θ.toLinearMap) = ⊥ ∨ (LinearMap.ker θ.toLinearMap) = ⊤ := by
    exact hρ (LinearMap.ker θ.toLinearMap) (repHom_kernel_isInvariantSubmodule ρ ψ θ)
  have hran : (LinearMap.range θ.toLinearMap) = ⊥ ∨ (LinearMap.range θ.toLinearMap) = ⊤ := by
    exact hψ (LinearMap.range θ.toLinearMap) (repHom_image_isInvariantSubmodule ρ ψ θ)

  by_cases h : θ = zeroRepHom ρ ψ
  . left
    assumption
  . right
    obtain hker|hker := hker
    . unfold Bijective
      constructor
      . apply (injective_iff_map_eq_zero' θ.toLinearMap).mpr
        intro v
        constructor
        . intro hv
          have hv : v ∈ (LinearMap.ker θ.toLinearMap) := by exact hv
          rw [hker] at hv
          exact hv
        . intro hv
          rw [hv]
          simp
      . obtain hran|hran := hran
        . exfalso
          have hker' : (LinearMap.ker θ.toLinearMap) = ⊤ := by
            apply Submodule.eq_top_iff'.mpr
            intro v
            apply LinearMap.mem_ker.mpr
            have hv : θ.toLinearMap v ∈ (⊥ : Submodule k W) := by
              rw [← hran]
              exact LinearMap.mem_range_self (RepresentationHom.toLinearMap ρ ψ) v
            exact hv
          rw [hker'] at hker
          have ct : ¬ Nontrivial V := by
            by_contra t
            have t' : ¬ (⊤ : (Submodule k V)) = (⊥ : (Submodule k V)) := by
              exact Ne.symm bot_ne_top
            contradiction
          contradiction
        . unfold Surjective
          intro w
          have hw : w ∈ (LinearMap.range θ.toLinearMap) := by
            rw [hran]
            exact _root_.trivial
          exact hw
    . exfalso
      have h' : θ = zeroRepHom ρ ψ := by {
        ext v
        calc θ.toLinearMap v = 0 := by{
          refine LinearMap.mem_ker.mp ?_
          rw [hker]
          exact _root_.trivial
        }
      }
      contradiction
  }

/- Endomorphisms of irreducible representations over algebraically closed fields are given by multiplication with a scalar. -/
theorem endomorphism_irreducibleRep_scalar {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
  (ρ : Representation k G V) (θ : RepresentationHom ρ ρ) : IsIrreducible ρ → ∃ s : k, ∀ v : V, θ v = s • v := by
  intro hρ
  obtain ⟨s, hs⟩ := Module.End.exists_eigenvalue (θ : V →ₗ[k] V)
  use s
  /- Define new ReprHom (θ-s1) -/
  let rh : (RepresentationHom ρ ρ) := ⟨θ.toLinearMap - s • LinearMap.id, by {
    intro g v
    simp
    apply θ.reprStructure}⟩

  /- rh is not Injective -/
  have ninjrh : ¬ Injective rh := by
    unfold Injective
    simp
    obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hs
    use v
    use 0
    unfold Module.End.HasEigenvector at hv
    constructor
    . simp [rh]
      obtain ⟨hv, _⟩ := hv
      rw [Module.End.eigenspace_def] at hv
      simp at hv
      assumption
    . exact hv.2

  /- rh is not Bijective -/
  have nbijrh : ¬ Bijective rh := by
    unfold Bijective
    push_neg
    intro ct
    exfalso
    contradiction

  /- rh is 0 -/
  have rh0 : rh = zeroRepHom ρ ρ := by
    obtain hrh := repHom_betweenIrreducibles_isZeroOrIso ρ ρ rh
    obtain hrh|hrh := hrh hρ hρ
    . assumption
    . exfalso
      contradiction

  intro v
  calc
    θ v = (θ v - s • v) + s • v := by simp
      _ = rh v + s • v          := by simp [rh]
      _ = s • v                 := by simp; rw [rh0]; rfl
