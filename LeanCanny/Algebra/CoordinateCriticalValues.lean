/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericProjectionFinite
public import LeanCanny.Algebra.CriticalValueAlgebraic

/-! # Exceptional coordinate values on a fixed hypersurface

At a regular critical point of a coordinate projection, every non-base
partial derivative vanishes. The chain rule forces every coefficient-field
derivation to kill the base coordinate, so that coordinate is algebraic.
Minimal-prime annihilators then produce one nonzero polynomial vanishing on
all these sweep values. No effective degree or coefficient bound is claimed.
-/

@[expose] public section

namespace LeanCanny.Algebra.CoordinateCriticalValues
open MvPolynomial
open scoped BigOperators

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem algebraic_coordinate [CharZero K] (q : MvPolynomial ι K) (base : ι) (x : ι → L)
    (hq : aeval x q = 0) (hb : aeval x (pderiv base q) ≠ 0)
    (hother : ∀ i, i ≠ base → aeval x (pderiv i q) = 0) : IsAlgebraic K (x base) := by
  classical
  apply TranscendentalDerivation.algebraic_of_all_derivations_vanish
  intro δ
  have he : δ (aeval x q) = 0 := by rw [hq, map_zero]
  rw [CriticalValueAlgebraic.chain_rule] at he
  have hsum : ∑ i, aeval x (pderiv i q) * δ (x i) = aeval x (pderiv base q) * δ (x base) := by
    apply Finset.sum_eq_single base
    · intro i _ hi
      rw [hother i hi, zero_mul]
    · simp
  rw [hsum] at he
  exact (mul_eq_zero.mp he).resolve_left hb

def direction (base : ι) : ι → K := fun i => if i = base then 1 else 0

noncomputable def ideal (q : MvPolynomial ι K) (base : ι) : Ideal (MvPolynomial (Option ι) K) :=
  GenericProjectionFinite.ideal q base (direction (K := K) base)

theorem quotient_coordinate_algebraic [CharZero K] (q : MvPolynomial ι K) (base : ι)
    (P : Ideal (MvPolynomial (Option ι) K)) [P.IsPrime] (hle : ideal q base ≤ P) :
    IsAlgebraic K (FiniteAlgebraicZeros.quotientPoint P (some base)) := by
  let F := FractionRing (MvPolynomial (Option ι) K ⧸ P)
  let z : Option ι → F := FiniteAlgebraicZeros.quotientPoint P
  have hz : ∀ j, aeval z (GenericProjectionFinite.equation q base (direction (K := K) base) j) = 0 := by
    intro j
    rw [FiniteAlgebraicZeros.eval_quotientPoint,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_range_self j))), map_zero]
  obtain ⟨hq, hinv, hpartial⟩ := (GenericProjectionFinite.equations_iff q base (direction (K := K) base) z).mp hz
  apply algebraic_coordinate q base (fun i => z (some i)) hq ?_ ?_
  · intro h
    rw [h, mul_zero] at hinv
    exact zero_ne_one hinv
  · intro i hi
    simpa [direction, hi] using hpartial i

theorem exists_annihilator [CharZero K] (q : MvPolynomial ι K) (base : ι) :
    ∃ d : Polynomial K, d ≠ 0 ∧
      Polynomial.aeval (X (some base) : MvPolynomial (Option ι) K) d ∈ (ideal q base).radical := by
  classical
  let I := ideal q base
  let S := I.minimalPrimes
  let : Fintype S := I.finite_minimalPrimes_of_isNoetherianRing.fintype
  have h (P : S) : ∃ d : Polynomial K, d ≠ 0 ∧
      Polynomial.aeval (X (some base) : MvPolynomial (Option ι) K) d ∈ P.val := by
    let : P.val.IsPrime := P.property.isPrime
    exact FiniteAlgebraicZeros.exists_mem_prime P.val (some base)
      (quotient_coordinate_algebraic q base P.val P.property.le)
  choose d hd hm using h
  refine ⟨∏ P : S, d P, Finset.prod_ne_zero_iff.mpr (fun P _ => hd P), ?_⟩
  change Polynomial.aeval (X (some base) : MvPolynomial (Option ι) K) (∏ P : S, d P) ∈ I.radical
  rw [← I.sInf_minimalPrimes, Ideal.mem_sInf]
  intro P hP
  rw [map_prod]
  exact P.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨P, hP⟩ : S))) (hm ⟨P, hP⟩)

omit [Fintype ι] in
theorem eval_annihilator (q : MvPolynomial ι K) (base : ι) (d : Polynomial K)
    (hd : Polynomial.aeval (X (some base) : MvPolynomial (Option ι) K) d ∈ (ideal q base).radical)
    (x : ι → L) (hq : aeval x q = 0) (hb : aeval x (pderiv base q) ≠ 0)
    (hother : ∀ i, i ≠ base → aeval x (pderiv i q) = 0) : Polynomial.aeval (x base) d = 0 := by
  let z : Option ι → L := fun i => i.elim (aeval x (pderiv base q))⁻¹ x
  have hz : ∀ j, aeval z (GenericProjectionFinite.equation q base (direction (K := K) base) j) = 0 := by
    apply (GenericProjectionFinite.equations_iff q base (direction (K := K) base) z).mpr
    refine ⟨hq, inv_mul_cancel₀ hb, ?_⟩
    intro i
    by_cases hi : i = base
    · simp [hi, direction]
    · simpa [direction, hi, z] using hother i hi
  have hI : ideal q base ≤ RingHom.ker (aeval z).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hz j
  obtain ⟨n, hn⟩ := hd
  have he := hI hn
  change aeval z ((Polynomial.aeval (X (some base) : MvPolynomial (Option ι) K) d) ^ n) = 0 at he
  rw [map_pow, ← Polynomial.aeval_algHom_apply, aeval_X] at he
  exact eq_zero_of_pow_eq_zero he

end LeanCanny.Algebra.CoordinateCriticalValues
