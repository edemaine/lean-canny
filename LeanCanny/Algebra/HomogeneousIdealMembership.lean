/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveNullstellensatz

/-! # Homogeneous multipliers for homogeneous ideal membership

Taking the desired homogeneous component of an arbitrary ideal expression
gives homogeneous multipliers of the complementary degrees. Inputs above
the desired degree have zero multiplier. This makes ideal membership
compatible with finite graded multiplication matrices.
-/

@[expose] public section

namespace LeanCanny.Algebra.HomogeneousIdealMembership
open scoped Classical BigOperators
variable {σ ι R : Type*} [CommRing R]

theorem component_mul_of_le (p q : MvPolynomial σ R) (d t : ℕ) (hp : p.IsHomogeneous d) (hdt : d ≤ t) :
    MvPolynomial.homogeneousComponent t (q * p) = MvPolynomial.homogeneousComponent (t - d) q * p := by
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hq := MvPolynomial.isHomogeneous_monomial (d := m) a rfl
    rw [MvPolynomial.homogeneousComponent_of_mem (hq.mul hp), MvPolynomial.homogeneousComponent_of_mem hq]
    have he : t = m.degree + d ↔ t - d = m.degree := by omega
    simp only [he, ite_mul, zero_mul]
  | add q r hq hr => simp only [add_mul, map_add, hq, hr]

theorem component_mul_eq_zero_of_lt (p q : MvPolynomial σ R) (d t : ℕ) (hp : p.IsHomogeneous d) (htd : t < d) :
    MvPolynomial.homogeneousComponent t (q * p) = 0 := by
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    have hq := MvPolynomial.isHomogeneous_monomial (d := m) a rfl
    rw [MvPolynomial.homogeneousComponent_of_mem (hq.mul hp), ite_eq_right (by omega)]
  | add q r hq hr => simp only [add_mul, map_add, hq, hr, add_zero]

theorem exists_homogeneous_multipliers [Fintype ι] (p : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (t : ℕ) (f : MvPolynomial σ R) (hf : f.IsHomogeneous t)
    (hmem : f ∈ ProjectiveNullstellensatz.generated p) :
    ∃ q : ι → MvPolynomial σ R, (∀ i, (q i).IsHomogeneous (t - d i)) ∧
      (∀ i, t < d i → q i = 0) ∧ (∑ i, q i * p i) = f := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  let v := fun i => if d i ≤ t then MvPolynomial.homogeneousComponent (t - d i) (q i) else 0
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    dsimp only [v]
    split
    · exact MvPolynomial.homogeneousComponent_isHomogeneous _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  · intro i hi
    exact ite_eq_right (Nat.not_le.mpr hi)
  · have he := congrArg (MvPolynomial.homogeneousComponent t) hq
    rw [map_sum, MvPolynomial.homogeneousComponent_eq_self hf] at he
    calc
      _ = ∑ i, MvPolynomial.homogeneousComponent t (q i * p i) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [v]
        by_cases hi : d i ≤ t
        · rw [ite_eq_left hi, component_mul_of_le _ _ _ _ (hp i) hi]
        · rw [ite_eq_right hi, zero_mul, component_mul_eq_zero_of_lt _ _ _ _ (hp i) (Nat.lt_of_not_ge hi)]
      _ = f := he

theorem multiplier_support_grade [Fintype ι] (p : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (t : ℕ) (f : MvPolynomial σ R) (hf : f.IsHomogeneous t)
    (hmem : f ∈ ProjectiveNullstellensatz.generated p) :
    ∃ q : ι → MvPolynomial σ R, (∀ i m, m ∈ (q i).support → m.degree + d i = t) ∧ (∑ i, q i * p i) = f := by
  obtain ⟨q, hq, hzero, hsum⟩ := exists_homogeneous_multipliers p d hp t f hf hmem
  refine ⟨q, ?_, hsum⟩
  intro i m hm
  have hd : d i ≤ t := by
    by_contra hn
    rw [hzero i (Nat.lt_of_not_ge hn)] at hm
    simp only [MvPolynomial.support_zero, Finset.notMem_empty] at hm
  have he : m.degree = t - d i := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hm) ((hq i).coeff_eq_zero hn)
  omega

end LeanCanny.Algebra.HomogeneousIdealMembership
