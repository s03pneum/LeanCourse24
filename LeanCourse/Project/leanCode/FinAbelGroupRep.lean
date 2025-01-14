import LeanCourse.Project.leanCode.RepresentationHom

open Function Set Classical
noncomputable section

namespace Representation

/-
# Goal: A representation of a finite abelian group is irreducible if and only if its degree is 1.

Note: By a representation, we mean a representation with finite dimension.
This seems reasonable since FDRep from does constrict itself to finite dimensional representations as well.

- Representations of degree 1 are irreducible. (This is `rep_degreeOne_irreducible` in `InvariantSubspaces`.)
- We prove the other direction for finite abelian groups,
  so take an irreducible representation of a finite abelian group, assume its dimension was not 1.
  - Thus, the dimension must be greater than 1 (generally assuming the representation to be non-trivial.)
  - Thus, the representation has a proper subspace of dimension 1.
  - In a representation of a finite abelian group, every subspace of dimension 1 is invariant.
  - Thus, the representation is not irreducible, so q.e.d. by contradiction.

(This proof is analogous to https://proofwiki.org/wiki/Irreducible_Representations_of_Abelian_Group)

-/


/- Representations of finite abelian groups are irreducible iff their degree is 1 -/
theorem rep_of_CommGroup_irreducible_iff_degree_one {k G V : Type*}
  [Field k] [IsAlgClosed k] [CommGroup G] [AddCommGroup V] [Module k V] [Nontrivial V] [FiniteDimensional k V]
  (ρ : Representation k G V) : IsIrreducible ρ ↔ degree ρ = 1 := by
  constructor
  . intro h
    by_contra ct

    /-V has a dimension greater than 1-/
    have dimVgt1 : Module.rank k V > 1 := by
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

    /-Every subspace of dimension 1 is invariant-/
    have subspaceDim1Invariant : ∀ U : (Submodule k V), (Module.rank k U) = 1 → IsInvariantSubmodule U ρ := by {
      unfold IsInvariantSubmodule
      intro U dimU g u
      have hs : ∃ s : k, ∀ v : V, (ρ g) v = s • v := by
        exact endomorphism_irreducibleRep_scalar ρ (rep_yields_repHom_commMonoid ρ g) h
      obtain ⟨s, hs⟩ := hs
      specialize hs u
      rw [hs]
      refine Submodule.smul_mem U s ?intro.h
      exact Submodule.coe_mem u
    }

    /-This yields the contradiction to V being irreducible-/
    obtain ⟨U, hU⟩ := oneDimSub
    have hU' : IsInvariantSubmodule U ρ := by apply subspaceDim1Invariant; exact
      Module.rank_eq_one_iff_finrank_eq_one.mpr hU
    specialize h U hU'
    obtain h|h := h
    . have h' : (Module.finrank k U) = 0 := by rw [h]; simp
      rw [h'] at hU
      simp at hU
    . have h' : (Module.finrank k U) = (Module.finrank k V) := by rw [h]; exact finrank_top k V
      rw [hU] at h'
      have h'' : (Module.rank k V) = 1 := by exact Module.rank_eq_one_iff_finrank_eq_one.mpr (id (Eq.symm h'))
      rw [h''] at dimVgt1
      simp at dimVgt1
  . exact rep_degreeOne_irreducible ρ
