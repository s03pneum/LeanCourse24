import Mathlib
open Function Set Classical
noncomputable section

namespace Representation

/-- A predicate for a subspace being invariant -/
abbrev IsInvariantSubspace {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (U : Submodule k V) (ρ : Representation k G V) :=
  ∀ g : G, ∀ u : U, ρ g u ∈ U

/-- A predicate for a representation being irreducible -/
abbrev IsIrreducible {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [Nontrivial V]
  (ρ : Representation k G V) :=
  ∀ U : Submodule k V, IsInvariantSubspace U ρ → U = 0 ∨ U = ⊤

/-- defines degree of a representation as rank of its module -/
def degree {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) : Cardinal := (Module.rank k V)

/-- Definition of Homomorhpisms between Representations -/
@[ext] class RepresentationHom {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) extends LinearMap (RingHom.id k) V W where
  reprStructure : ∀ g : G, ∀ v : V, toLinearMap (ρ g v) = ψ g (toLinearMap v)

/-- Coercions of RepresentationHom to Function and Linear Map-/
instance {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] {ρ : Representation k G V} {ψ : Representation k G W} : CoeFun (RepresentationHom ρ ψ) (fun _ ↦ V →ₗ[k] W) where
  coe := by
    intro θ
    use ⟨θ.toFun, ?_⟩
    simp; intro x y; simp

instance {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W] {ρ : Representation k G V} {ψ : Representation k G W} : CoeFun (RepresentationHom ρ ψ) (fun _ ↦ V → W) where
  coe := by intro rh; use rh.toFun

/- The zero linear map is a representation hom -/
instance zeroReprHom {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) : (RepresentationHom ρ ψ) where
  toFun := fun v ↦ 0
  map_add' := by intro x y; simp
  map_smul' := by intro m x; simp
  reprStructure := by intro h v; simp

/- A Representation of Degree One is Irreducible -/
theorem repr_degreeOne_irreducible {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V] [Nontrivial V]
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

/- The image of a reprHom is an Invariant Subspace -/
theorem reprHom_image_isInvariantSubspace {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) (θ : (RepresentationHom ρ ψ)) :
  IsInvariantSubspace (LinearMap.range θ.toLinearMap) ψ := by
  simp [IsInvariantSubspace]
  intro g v
  use (ρ g) v
  exact θ.reprStructure g v

/- The kernel of a reprHom is an Invariant Subspace -/
theorem reprHom_kernel_isInvariantSubspace {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
  (ρ : Representation k G V) (ψ : Representation k G W) (θ : (RepresentationHom ρ ψ)) :
  IsInvariantSubspace (LinearMap.ker θ.toLinearMap) ρ := by
  simp [IsInvariantSubspace]
  intro g v vinker
  calc
    θ ((ρ g) v) = ψ g (θ.toLinearMap v) := by exact θ.reprStructure g v
              _ = ψ g 0                 := by rw [vinker]
              _ = 0                     := by exact LinearMap.map_zero (ψ g)

/- ReprHoms between irreducible representations are zero or isomorphisms -/
theorem reprHom_betweenIrreducibles_isZeroOrIso {k G V W : Type*} [CommSemiring k] [Monoid G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Nontrivial V] [Nontrivial W]
  (ρ : Representation k G V) (ψ : Representation k G W) (θ : (RepresentationHom ρ ψ)) :
  IsIrreducible ρ → IsIrreducible ψ →  θ = zeroReprHom ρ ψ ∨ Bijective θ := by {
  intro hρ hψ
  have hker : (LinearMap.ker θ.toLinearMap) = ⊥ ∨ (LinearMap.ker θ.toLinearMap) = ⊤ := by exact hρ (LinearMap.ker θ.toLinearMap) (reprHom_kernel_isInvariantSubspace ρ ψ θ)
  have hran : (LinearMap.range θ.toLinearMap) = ⊥ ∨ (LinearMap.range θ.toLinearMap) = ⊤ := by exact hψ (LinearMap.range θ.toLinearMap) (reprHom_image_isInvariantSubspace ρ ψ θ)

  by_cases h : θ = zeroReprHom ρ ψ
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
      have h' : θ = zeroReprHom ρ ψ := by {
        ext v
        calc θ.toLinearMap v = 0 := by{
          refine LinearMap.mem_ker.mp ?_
          rw [hker]
          exact _root_.trivial
        }
      }
      contradiction
  }

instance repr_yields_reprHom_commMonoid {k G V : Type*} [CommSemiring k] [CommMonoid G] [AddCommMonoid V] [Module k V]
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

/- Every endomorphism of an irreducible representation over an algebraically closed field is given by multiplication with a scalar-/
theorem endomorphism_irreducibleRepr_scalar {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
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
  have rh0 : rh = zeroReprHom ρ ρ := by
    obtain hrh := reprHom_betweenIrreducibles_isZeroOrIso ρ ρ rh
    obtain hrh|hrh := hrh hρ hρ
    . assumption
    . exfalso
      contradiction

  intro v
  calc
    θ v = (θ v - s • v) + s • v := by simp
      _ = rh v + s • v          := by simp [rh]
      _ = s • v                 := by simp; rw [rh0]; rfl

/- Representations of finite abelian groups are irreducible iff their degree is 1 -/
theorem repr_of_CommGroup_irreducible_iff_degree_one {k G V : Type*} [Field k] [IsAlgClosed k] [CommGroup G] [AddCommGroup V] [Module k V] [Nontrivial V] [FiniteDimensional k V]
  (ρ : Representation k G V) : IsIrreducible ρ ↔ degree ρ = 1 := by
  constructor
  . intro h
    /-Every subspace of dimension 1 is invariant-/
    have subspaceDim1Invariant : ∀ U : (Submodule k V), (Module.rank k U) = 1 → IsInvariantSubspace U ρ := by {
      unfold IsInvariantSubspace
      intro U dimU g u
      have hs : ∃ s : k, ∀ v : V, (ρ g) v = s • v := by
        exact endomorphism_irreducibleRepr_scalar ρ (repr_yields_reprHom_commMonoid ρ g) h
      obtain ⟨s, hs⟩ := hs
      specialize hs u
      rw [hs]
      refine Submodule.smul_mem U s ?intro.h
      exact Submodule.coe_mem u
    }
    by_contra ct

    /-V has a dimension greater than 1-/
    have dimV : Module.rank k V > 1 := by
      by_contra dle1
      simp at dle1
      have dc : ((Module.rank k V)) = 0 ∨ (Module.rank k V) = 1 := by
        have dc' : (Module.rank k V) < 1 ∨ (Module.rank k V) = 1 := by
          apply le_iff_lt_or_eq.mp
          assumption
        obtain dc'|dc' := dc'
        . left
          apply Cardinal.lt_one_iff_zero.mp
          assumption
        . right
          assumption
      obtain dc|dc := dc
      . have pbn : 0 < (Module.rank k V) := by
          apply rank_pos_iff_nontrivial.mpr
          rename_i ntv
          assumption
        rw [← dc] at pbn
        simp at pbn
      . simp[degree] at ct
        contradiction

    /-V has a subspace U with dimension 1-/
    have oneDimSub : ∃ U : (Submodule k V), (Module.finrank k U) = 1 := by
      have nte : ∃ u : V, u ≠ 0 := by exact exists_ne 0
      obtain ⟨u, nte⟩ := nte
      use Submodule.span k {u}
      apply finrank_span_singleton
      assumption

    /-This yields the contradiction to V being irreducible-/
    obtain ⟨U, hU⟩ := oneDimSub
    have hU' : IsInvariantSubspace U ρ := by apply subspaceDim1Invariant; exact
      Module.rank_eq_one_iff_finrank_eq_one.mpr hU
    specialize h U hU'
    obtain h|h := h
    . have h' : (Module.finrank k U) = 0 := by rw [h]; simp
      rw [h'] at hU
      simp at hU
    . have h' : (Module.finrank k U) = (Module.finrank k V) := by rw [h]; exact finrank_top k V
      rw [hU] at h'
      have h'' : (Module.rank k V) = 1 := by exact Module.rank_eq_one_iff_finrank_eq_one.mpr (id (Eq.symm h'))
      rw [h''] at dimV
      simp at dimV
  . exact repr_degreeOne_irreducible ρ
