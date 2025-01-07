import Mathlib
import LeanCourse.Project.leanCode.RepresentationHom

/- open namespaces that you use to shorten names and enable notation. -/
open Function Set Classical Representation
noncomputable section

theorem representationIrreducibility_equiv_simpleModule {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Nontrivial V]
  (ρ : Representation k G V) : ρ.IsIrreducible ↔ IsSimpleModule (MonoidAlgebra k G) ρ.asModule:= by{
  constructor
  . intro h
    refine isSimpleOrder_iff_isAtom_top.mpr ?mp.a
    /- Proof by contradiction-/
    by_contra ct

    /- There is a proper submodule over kG-/
    have h' : ∃ U : (Submodule (MonoidAlgebra k G) ρ.asModule), U ≠ ⊥ ∧ U ≠ ⊤ := by {
      have defAtom : ¬ (⊤ ≠ (⊥ : (Submodule (MonoidAlgebra k G) ρ.asModule)) ∧
        ∀ W : (Submodule (MonoidAlgebra k G) ρ.asModule), W ≠ ⊥ → W ≤ ⊤ → ⊤ ≤ W) := by{
          by_contra tc
          have ct' : IsAtom (⊤ : (Submodule (MonoidAlgebra k G) ρ.asModule)) := by
            exact isAtom_iff_le_of_ge.mpr tc
          contradiction
        }
      push_neg at defAtom
      have top_neq_bot : ⊤ ≠ (⊥ : (Submodule (MonoidAlgebra k G) ρ.asModule)) := by
        refine (Submodule.ne_bot_iff ⊤).mpr ?_
        have nontrV : ∃ x : V, x ≠ 0 := by exact exists_ne 0
        have nontrAsModule : ∃ x : ρ.asModule, x ≠ 0 := by
          obtain ⟨x, hx⟩ := nontrV
          use x
        obtain ⟨x, hx⟩ := nontrAsModule
        use x
        constructor
        . exact _root_.trivial
        . assumption
      specialize defAtom top_neq_bot
      obtain ⟨W, hW⟩ := defAtom
      use W
      constructor
      . exact hW.left
      . obtain ⟨_, ⟨_, hW⟩⟩ := hW
        simp at hW
        assumption
    }
    obtain ⟨U, hU⟩ := h'

    /- FINE UNTIL HERE-/

    have ht : ¬ρ.IsIrreducible := by{
      unfold Representation.IsIrreducible
      push_neg

      sorry
    }
    contradiction
  . sorry
}

/- Old try, we try to repair this above-/

/- A representation is irreducible iff the corresponding module is simple-/
theorem representationIrreducibility_equiv_simpleModule' {k G V : Type*} [CommRing k] [Monoid G] [AddCommGroup V] [Module k V] [Nontrivial V]
  (ρ : Representation k G V) : ρ.IsIrreducible ↔ IsSimpleModule (MonoidAlgebra k G) ρ.asModule:= by
    constructor
    . intro h
      refine isSimpleOrder_iff_isAtom_top.mpr ?mp.a
      /- Proof by contradiction-/
      by_contra ct

      /- There is a proper submodule over kG-/
      have h' : ∃ U : (Submodule (MonoidAlgebra k G) ρ.asModule), U ≠ ⊥ ∧ U ≠ ⊤ := by {
        have defAtom : ¬ (⊤ ≠ (⊥ : (Submodule (MonoidAlgebra k G) ρ.asModule)) ∧
          ∀ W : (Submodule (MonoidAlgebra k G) ρ.asModule), W ≠ ⊥ → W ≤ ⊤ → ⊤ ≤ W) := by{
            by_contra tc
            have ct' : IsAtom (⊤ : (Submodule (MonoidAlgebra k G) ρ.asModule)) := by
              exact isAtom_iff_le_of_ge.mpr tc
            contradiction
          }
        push_neg at defAtom
        have top_neq_bot : ⊤ ≠ (⊥ : (Submodule (MonoidAlgebra k G) ρ.asModule)) := by
          refine (Submodule.ne_bot_iff ⊤).mpr ?_
          have nontrV : ∃ x : V, x ≠ 0 := by exact exists_ne 0
          have nontrAsModule : ∃ x : ρ.asModule, x ≠ 0 := by
            obtain ⟨x, hx⟩ := nontrV
            use x
          obtain ⟨x, hx⟩ := nontrAsModule
          use x
          constructor
          . exact _root_.trivial
          . assumption
        specialize defAtom top_neq_bot
        obtain ⟨W, hW⟩ := defAtom
        use W
        constructor
        . exact hW.left
        . obtain ⟨_, ⟨_, hW⟩⟩ := hW
          simp at hW
          assumption
      }
      obtain ⟨U, hU⟩ := h'

      /- There is an invariant subspace of ρ-/
      have ht : ¬ρ.IsIrreducible := by{
        unfold Representation.IsIrreducible
        push_neg
        /- Convert U to a Module over k-/
        have U' : Submodule k V := ⟨⟨⟨U.carrier, by{
          simp
          intro a b ha hb
          exact (Submodule.add_mem_iff_right U ha).mpr hb
        }⟩, by simp⟩, by {
          simp
          intro r u hu
          let r' : (MonoidAlgebra k G) := r • 1
          have huMod : ∀ w, w ∈ U → r' • w ∈ U := by exact fun w a ↦ Submodule.smul_mem U r' a
          specialize huMod u hu
          have tsst : IsScalarTower k (MonoidAlgebra k G) ρ.asModule := by
            refine { smul_assoc := ?smul_assoc }
            intro x a b
            sorry
          have test : r • u = (@HSMul.hSMul (MonoidAlgebra k G) ρ.asModule ρ.asModule instHSMul r' u) := by
            symm
            calc
              (@HSMul.hSMul (MonoidAlgebra k G) ρ.asModule ρ.asModule instHSMul r' u) = (@HSMul.hSMul (MonoidAlgebra k G) ρ.asModule ρ.asModule instHSMul (r • 1) u) := by rfl
              _ = r • (@HSMul.hSMul (MonoidAlgebra k G) ρ.asModule ρ.asModule instHSMul 1 u) := by{
                apply smul_assoc
              }
              _ = r • u := by {
                have tt' : @HSMul.hSMul (MonoidAlgebra k G) ρ.asModule ρ.asModule instHSMul 1 u  = u := by
                  sorry
                rw [tt']
              }
          rw [test]
          assumption
        }⟩
        use U'
        constructor
        . sorry
        . sorry
      }
      contradiction
    . sorry
