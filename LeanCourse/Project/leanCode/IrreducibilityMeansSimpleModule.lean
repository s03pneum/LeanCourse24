import Mathlib
import LeanCourse.Project.leanCode.RepresentationHom

open Function Set Classical
noncomputable section

namespace Representation

/-
# Overview
- `representationAction_asSmul` translates the action of a group element to a scalar
  multiplication in the corresponding kG-module
- `smul_kModule_to_kGmodule` translates scalar multiplication in module of representation
  to scalar multiplication in the corresponding kG-module
- `asSubmodule` constructs a Submodule of (MonoidAlgebra k G) from an invariant submodule
- `ofSubmodule` constructs a Submodule of ρ from a submodule of the corresponding kG-module
- `ofSubmodule_isIrreducible` submodule constructed by Representation.ofSubmodule is invariant
- `nonSimpleModule_has_nontrivialSubmodule` if a module is not simple, it has a submodule that is neither ⊤ nor ⊥
- `representationIrreducible_equiv_simpleModule` Representation is irreducible iff corresponding kG-module is simple
-/

/- Representation action as scalar multiplication over Monoid Algebra-/
theorem representationAction_asSmul {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (g : G) (u : ρ.asModule) : (ρ g) u = ((MonoidAlgebra.single) g (1 : k)) • u := by
  symm
  calc
    ρ.asModuleEquiv (((MonoidAlgebra.single) g (1 : k)) • u) = (ρ.asAlgebraHom ((MonoidAlgebra.single) g (1 : k))) (ρ.asModuleEquiv u) := by rfl
    _ = (ρ.asAlgebraHom ((MonoidAlgebra.single) g (1 : k))) u := by rfl
    _ = (ρ g) u := by refine LinearMap.congr_fun ?h u; exact asAlgebraHom_single_one ρ g

/- Scalar multiplication in k-module as scalar multiplication in corresponding kG-module-/
theorem smul_kModule_to_kGmodule {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (c : k) (v : ρ.asModule) : c • v = ρ.asModuleEquiv ((MonoidAlgebra.single (1 : G) c) • v) := by
  symm
  calc
    ρ.asModuleEquiv ((MonoidAlgebra.single (1 : G) c) • v) = (ρ.asAlgebraHom (MonoidAlgebra.single (1 : G) c)) (ρ.asModuleEquiv v) := by rfl
    _ = (ρ.asAlgebraHom (MonoidAlgebra.single (1 : G) c)) v := by rfl
    _ = (c • ρ (1 : G)) v := by rw [asAlgebraHom_single]
    _ = c • ((ρ 1) v) := by rfl
    _ = c • ((1 : V →ₗ[k] V) v) := by rw [MonoidHom.map_one ρ]
    _ = c • v := by simp

/- An invariant submodule corresponds to a submodule of ρ.asModule-/
instance asSubmodule {k G V: Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U : Submodule k V) (hU : IsInvariantSubmodule U ρ): (Submodule (MonoidAlgebra k G) ρ.asModule) where
  carrier := U.carrier
  add_mem' := by
    simp
    intro a b aU bU
    exact Submodule.add_mem U aU bU
  zero_mem' := by simp
  smul_mem' := by
    simp
    intro r x xU
    rw [← MonoidAlgebra.sum_single r]
    have asFinSum : Finsupp.sum r MonoidAlgebra.single • x = (∑ g ∈ r.support, MonoidAlgebra.single g (r g)) • x := by rfl
    rw [asFinSum]
    rw [Finset.sum_smul]
    apply Submodule.sum_mem
    intro g grsupp
    have transAlgebraRepr : (MonoidAlgebra.single g (r g) • x) = (r g) • (ρ g (ρ.asModuleEquiv x)) := by {
      calc
        (MonoidAlgebra.single g (r g) • x) = (ρ.asAlgebraHom (MonoidAlgebra.single g (r g))) (ρ.asModuleEquiv x) := by rfl
        _ = (r g) • (ρ g (ρ.asModuleEquiv x)) := by rw [Representation.asAlgebraHom_single]; simp
    }
    rw [transAlgebraRepr]
    refine Submodule.smul_mem U (r g) ?_
    unfold Representation.IsInvariantSubmodule at hU
    apply (hU g ⟨x, by assumption⟩)


/- A submodule of ρ.asModule corresponds to a k-submodule of V-/
instance ofSubmodule {k G V: Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U : Submodule (MonoidAlgebra k G) ρ.asModule) : (Submodule k ρ.asModule) where
  carrier := U.carrier
  add_mem' := by
    simp
    intro a b aU bU
    exact Submodule.add_mem U aU bU
  zero_mem' := by simp
  smul_mem' := by
    simp
    intro c v vU
    rw [smul_kModule_to_kGmodule]
    exact Submodule.smul_mem U (MonoidAlgebra.single 1 c) vU

/- The submodule constructed by Representation.ofSubmodule is invariant-/
theorem ofSubmodule_isInvariant {k G V: Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V) (U : Submodule (MonoidAlgebra k G) ρ.asModule) : IsInvariantSubmodule (ofSubmodule ρ U) ρ := by
  simp [IsInvariantSubmodule]
  intro g u uU'
  have theoCoerced : ((ρ g) u : ρ.asModule) ∈ ρ.ofSubmodule U := by
    rw [representationAction_asSmul ρ g u]
    have showAsCar : (((MonoidAlgebra.single) g (1 : k)) • u) ∈ U.carrier := by
      have smulInModule : (((MonoidAlgebra.single) g (1 : k)) • u) ∈ U := by exact Submodule.smul_mem U (MonoidAlgebra.single g 1) uU'
      assumption
    assumption
  assumption

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
      sorry
    exact h w (hWU wW) (hWU' wW)
  · intro W hW h'W w hw
    sorry

/- If a nontrivial module is not simple, it has a submodule that is neither ⊤ nor ⊥-/
lemma nonSimpleModule_has_nontrivialSubmodule {k V : Type*} [Ring k] [AddCommGroup V] [Module k V] [Nontrivial V]
   : ¬ IsSimpleModule k V → ∃ U : Submodule k V, U ≠ ⊥ ∧ U ≠ ⊤ := by{
  intro h
  by_contra t

  have nct : IsSimpleModule k V := by
    refine isSimpleOrder_iff_isAtom_top.mpr ?mp.a
    by_contra ct
    have defAtom : ¬ (⊤ ≠ (⊥ : Submodule k V) ∧ ∀ W : (Submodule k V), W ≠ ⊥ → W ≤ ⊤ → ⊤ ≤ W) := by
      by_contra tc
      have ct' : IsAtom (⊤ : Submodule k V) := by
        exact isAtom_iff_le_of_ge.mpr tc
      contradiction
    push_neg at defAtom
    have top_neq_bot : ⊤ ≠ (⊥ : Submodule k V) := by
      refine (Submodule.ne_bot_iff ⊤).mpr ?_
      have nontrV : ∃ x : V, x ≠ 0 := by exact exists_ne 0
      obtain ⟨x, hx⟩ := nontrV
      use x
      simp
      exact hx
    specialize defAtom top_neq_bot
    obtain ⟨W, hW⟩ := defAtom
    have t' : ∃ U, U ≠ (⊥ : Submodule k V) ∧ U ≠ (⊤ : Submodule k V) := by
      use W
      constructor
      . exact hW.1
      . simp at hW
        exact hW.2
    contradiction

  contradiction}

/- Theorem: Representation is irreducible iff corresponding kG-module is simple-/
theorem representationIrreducible_equiv_simpleModule {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Nontrivial V] [Finite G]
  (ρ : Representation k G V) : ρ.IsIrreducible ↔ IsSimpleModule (MonoidAlgebra k G) ρ.asModule:= by{
  constructor
  . /- Given irreducibility of representation, show simplicity of kG-module-/
    intro h

    /- Proof by contradiction-/
    by_contra ct

    /- Take submodule of kG-module-/
    have nontrAsModule: Nontrivial ρ.asModule := by assumption
    have h' : ∃ U : (Submodule (MonoidAlgebra k G) ρ.asModule), U ≠ ⊥ ∧ U ≠ ⊤ := by exact nonSimpleModule_has_nontrivialSubmodule ct
    obtain ⟨U, hU⟩ := h'

    /- Use that to show that ρ has irreducible submodule -/
    have ht : ¬ρ.IsIrreducible := by{
      unfold Representation.IsIrreducible
      push_neg

      let U' : Submodule k V := ofSubmodule ρ U
      use U'
      have U'Car : U'.carrier = U.carrier := by rfl
      have botCar : (⊥ : Submodule k V).carrier = {0} := by rfl
      constructor
      . exact ofSubmodule_isInvariant ρ U
      . constructor
        . by_contra t
          have uBot : U = ⊥ := by
            ext x
            constructor
            . intro xU
              have xUCar : x ∈ U.carrier := by exact xU
              have xBotCar : x ∈ (⊥ : Submodule (MonoidAlgebra k G) ρ.asModule).carrier := by
                rw [← U'Car] at xUCar
                rw [t] at xUCar
                assumption
              exact xBotCar
            . simp
              intro x0
              rw [x0]
              exact Submodule.zero_mem U
          obtain ⟨hU, _⟩ := hU
          contradiction
        . by_contra t
          have uTop : U = ⊤ := by
            ext x
            constructor
            . intro xU
              exact _root_.trivial
            . intro xTop
              have xUCar : x ∈ U.carrier := by
                rw [← U'Car]
                have carComp : U'.carrier = (⊤ : Submodule k V).carrier := by
                  exact
                    congrArg AddSubsemigroup.carrier
                      (congrArg AddSubmonoid.toAddSubsemigroup
                        (congrArg Submodule.toAddSubmonoid t))
                rw [carComp]
                simp
              exact xUCar
          obtain ⟨_, hU⟩ := hU
          contradiction
    }
    contradiction
  . /- Given simplicity of module, show irreducibility of representation-/
    intro h
    unfold Representation.IsIrreducible
    intro U hU

    let U' : Submodule (MonoidAlgebra k G) ρ.asModule := asSubmodule ρ U hU
    have U'trivial : U' = ⊥ ∨ U' = ⊤ := by exact eq_bot_or_eq_top U'
    have UU'Car : U.carrier = U'.carrier := by rfl
    obtain U'trivial|U'trivial := U'trivial
    . left
      simp
      ext x
      constructor
      . intro xU
        have xU'Car : x ∈ U'.carrier := by
          rw [← UU'Car]
          assumption
        rw [U'trivial] at xU'Car
        simp at xU'Car
        rw [xU'Car]
        rfl
      . intro xBot
        simp at xBot
        rw [xBot]
        exact Submodule.zero_mem U
    . right
      ext x
      constructor
      . intro xU
        exact _root_.trivial
      . intro xTop
        have xUCar : x ∈ U.carrier := by
          rw [UU'Car, U'trivial]
          simp
        assumption
}
