import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 8.2 and 9.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 26.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice.
Feel free to skip these exercises-/

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by {
  rw [← Ideal.span_union]
  rw [@span_gcd]
  rfl
  }

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by {
  ext k
  simp [Ideal.mem_span_singleton]
  exact Iff.symm lcm_dvd_iff
  }

/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {R M m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by intro A B; simp
    map_smul' := by intro r A; simp
    invFun := fun M ↦ Mᵀ
    left_inv := by simp [LeftInverse]
    right_inv := by simp [Function.RightInverse]; exact congrFun rfl

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [CharP R 2] (m : M) :
    m + m = 0 := by {
  calc
    m + m = (1 : R) •  m + (1 : R) •  m := by rw [one_smul]
        _ = ((1 : R) + (1 : R)) • m     := by rw [add_smul]
        _ = (0 : R) • m                 := by rw [CharTwo.add_self_eq_zero (1 : R)]
        _ = 0                           := by exact zero_smul R m
  }

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

#check RingHom.mk'
#check MonoidHom.mk'

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
  R →+* R := RingHom.mk' (MonoidHom.mk ⟨fun r ↦ r ^ p, by dsimp; exact one_pow p⟩
  (by simp; intro x y; ring))
  (by intro a b; simp; exact add_pow_char R a b)


@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := rfl

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by {
  induction n with
  | zero => simp
  | succ n ih => simp; rw [ih]; ring
  }

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by {
  simp [Injective]
  intro x y
  intro h
  have t : (x-y) ^ p = 0 := by
    calc
      (x - y) ^ p = x ^ p - y ^ p := by rw [sub_pow_expChar]
                _ = x ^ p - x ^ p := by rw [← h]
                _ = 0             := by ring
  have t' : (x-y) = 0 := by exact pow_eq_zero t
  calc
    x = y + (x - y) := by ring
    _ = y + (0 : R) := by rw [t']
    _ = y           := by ring
  }

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by {
  apply Function.Injective.bijective_of_finite
  exact frobeniusMorphism_injective p R
  }

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by {
  constructor
  . intro h
    rw [← iterate_frobeniusMorphism] at h
    let f := ⇑(frobeniusMorphism p R)
    have t : Function.Injective f^[k] := by
      refine Injective.iterate ?Hinj k;
      exact frobeniusMorphism_injective p R
    have t' : f^[k] (x) = f^[k] (1) := by simp [f]; rw [h]
    exact t (t (congrArg f^[k] t'))
  . intro h
    rw [h]
    ring
  }

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by {
  simp [IsSquare]
  have h : ∀ x, ∃ r, (frobeniusMorphism 2 R) r = x := by
    have t : Function.Surjective (frobeniusMorphism 2 R) := by
      apply Function.Bijective.surjective
      exact frobeniusMorphism_bijective 2 R
    exact fun x ↦ t x
  specialize h x
  obtain ⟨r, h⟩ := h
  use r
  rw [← h]
  simp
  ring
  }

end Frobenius


section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

def IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by {
  simp [IsAUnit]
  obtain ⟨x', hx⟩ := hx
  obtain ⟨y', hy⟩ := hy
  use (y' * x')
  calc
    y' * x' * (x * y) = y' * (x' * x) * y := by ring
                    _ = y' * y            := by rw [hx]; ring
                    _ = 1                 := by rw [hy]
  }

def IsAUnit.inv : {x : R // IsAUnit x} → {x : R // IsAUnit x} :=
  have h (r : {x : R // IsAUnit x}) : ∃ b : {x : R // IsAUnit x}, b.1*r = 1 := by
    obtain ⟨r', hr⟩ := r.2
    use ⟨r', by simp [IsAUnit]; use r; rw [mul_comm]; assumption⟩
  fun r ↦ Exists.choose (h r)

instance groupUnits : Group {x : R // IsAUnit x} where
  mul := fun r ↦ (fun s ↦ ⟨r.1*s.1, by
    simp [IsAUnit]
    obtain ⟨r', hr⟩ := r.2
    obtain ⟨s', hs⟩ := s.2
    use (s'*r')
    calc
      s' * r' * (↑r * ↑s) = s' * (r' * ↑r) * ↑s := by ring
                        _ = s' * s              := by rw [hr]; ring
                        _ = 1                   := by rw [hs]⟩)
  mul_assoc := by
    intro a b c
    ext
    apply mul_assoc
  one := ⟨1, by use 1; ring⟩
  one_mul := by
    intro a
    ext
    apply one_mul
  mul_one := by
    intro a
    ext
    apply mul_one
  inv := IsAUnit.inv
  inv_mul_cancel := by
    intro r
    have h (r : {x : R // IsAUnit x}) : ∃ b : {x : R // IsAUnit x}, b.1*r = 1 := by
      obtain ⟨r', hr⟩ := r.2
      use ⟨r', by simp [IsAUnit]; use r; rw [mul_comm]; assumption⟩
    have t : (IsAUnit.inv r : R) * r = 1 := by
      simp [IsAUnit.inv]
      exact Exists.choose_spec (h r)
    exact Eq.symm (Subtype.eq (id (Eq.symm t)))

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by rfl

end Ring

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
#check exists_ne
lemma commutative_of_module {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [IsDomain R] [CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p)
  · ext a
    simp
    constructor
    . intro ap
      by_cases t : a = 0
      . left
        assumption
      . right
        constructor
        exact zero_lt_of_ne_zero t
        assumption
    . intro h
      obtain h|h := h
      . rw [h]
        exact pos_of_neZero p
      . exact h.2
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by
    simp
    intro i ipos ip
    refine Prime.dvd_choose_self hp' ?hk ip
    exact not_eq_zero_of_lt ipos
  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by
      simp
      refine sum_eq_zero ?h
      intro k krange
      refine _root_.mul_eq_zero.mpr ?h.a
      right
      apply (CharP.cast_eq_zero_iff R p (p.choose k)).mpr
      apply dvd_choose
      assumption
    _ = 0 := by
      refine sum_eq_zero ?h
      intro r rrange
      ring
  rw [add_pow, Finset.sum_range_succ, range_eq_insert_Ioo]
  simp
  rw [h6]
  ring
  }


section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f x.1 + g x.2
  map_add' x y := by simp; module
  map_smul' r x := by simp

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f x + g y := rfl

lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
  constructor
  . intro h
    rw [h]
    constructor
    . ext x
      simp
    . ext x
      simp
  . rintro ⟨hl, hr⟩
    rw [← hl, ← hr]
    ext x
    rw [coproduct_def]
    simp
    rw [← LinearMap.map_add]
    simp
  }


end LinearMap
