/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalSpace

/-! # Integer specialization of bivariate coordinate annihilators

A fixed bound on the inner degree clears a rational parameter with the same
integer scale in every outer coefficient. The resulting integer polynomial
has the original outer degree bound, and its streamed coefficient reader is
obtained from the existing denominator-cleared univariate evaluator.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Polynomial MatrixPower
open scoped BigOperators Classical

noncomputable def clearCoefficient (D : ℕ) (a b : ℤ) (p : Polynomial ℤ) : ℤ :=
  (UnivariateRational.clear D p (C a) (C b)).eval 0

@[simp] theorem clearCoefficient_zero (D : ℕ) (a b : ℤ) : clearCoefficient D a b 0 = 0 := by
  simp [clearCoefficient, UnivariateRational.clear]

noncomputable def specialize (D : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ)) : Polynomial ℤ :=
  p.sum fun i q => monomial i (clearCoefficient D a b q)

@[simp] theorem specialize_coeff (D : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ)) (i : ℕ) :
    (specialize D a b p).coeff i = clearCoefficient D a b (p.coeff i) := by
  classical
  unfold specialize
  rw [Polynomial.coeff_sum]
  simp only [Polynomial.sum, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hi
    simp [Polynomial.notMem_support_iff.mp hi]

theorem specialize_degree_le (D : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ)) :
    (specialize D a b p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [specialize_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hi, clearCoefficient_zero]

theorem clearCoefficient_cast {K : Type*} [Field K] [CharZero K]
    (D : ℕ) (a b : ℤ) (p : Polynomial ℤ) (hp : p.natDegree ≤ D) (hb : (b : K) ≠ 0) :
    (clearCoefficient D a b p : K) = (b : K) ^ D * p.eval₂ (Int.castRingHom K) ((a : K) / (b : K)) := by
  have h := UnivariateRational.eval₂_clear (Int.castRingHom K) D p (C a) (C b) hp (0 : K)
    (by simpa using hb)
  have he := Polynomial.eval₂_at_apply (p := UnivariateRational.clear D p (C a) (C b)) (Int.castRingHom K) (0 : ℤ)
  have he' : (Int.castRingHom K) ((UnivariateRational.clear D p (C a) (C b)).eval (0 : ℤ)) =
      (UnivariateRational.clear D p (C a) (C b)).eval₂ (Int.castRingHom K) 0 := by
    simpa only [map_zero] using he.symm
  simpa only [clearCoefficient, Polynomial.eval₂_C, Int.coe_castRingHom] using he'.trans h

theorem specialize_map {K : Type*} [Field K] [CharZero K]
    (D : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ))
    (hp : ∀ i, (p.coeff i).natDegree ≤ D) (hb : (b : K) ≠ 0) :
    (specialize D a b p).map (Int.castRingHom K) =
      C ((b : K) ^ D) * p.map (Polynomial.eval₂RingHom (Int.castRingHom K) ((a : K) / (b : K))) := by
  ext i
  simp only [coeff_map, specialize_coeff, coeff_C_mul, Polynomial.coe_eval₂RingHom]
  exact clearCoefficient_cast D a b (p.coeff i) (hp i) hb

theorem specialize_ne_zero {K : Type*} [Field K] [CharZero K]
    (D : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ))
    (hp : ∀ i, (p.coeff i).natDegree ≤ D) (hb : (b : K) ≠ 0)
    (hne : p.map (Polynomial.eval₂RingHom (Int.castRingHom K) ((a : K) / (b : K))) ≠ 0) :
    specialize D a b p ≠ 0 := by
  intro hz
  have h := specialize_map D a b p hp hb
  rw [hz, Polynomial.map_zero] at h
  exact (mul_ne_zero (Polynomial.C_ne_zero.mpr (pow_ne_zero _ hb)) hne) h.symm

theorem specialize_eval_eq_zero {K : Type*} [Field K] [CharZero K]
    (D : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ))
    (hp : ∀ i, (p.coeff i).natDegree ≤ D) (hb : (b : K) ≠ 0) (x : K)
    (hx : (p.map (Polynomial.eval₂RingHom (Int.castRingHom K) ((a : K) / (b : K)))).eval x = 0) :
    (specialize D a b p).eval₂ (Int.castRingHom K) x = 0 := by
  rw [← Polynomial.eval_map, specialize_map D a b p hp hb, Polynomial.eval_mul,
    Polynomial.eval_C, hx, mul_zero]

end LeanCanny.ETR.TubeCoordinateAnnihilator

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Polynomial MatrixPower RationalSubstitution.IntegerBits
open scoped Classical

noncomputable def coefficientPolynomial (p : List Bool → Polynomial (Polynomial ℤ)) (c : List Bool) : Polynomial ℤ :=
  (p (pairFst c)).coeff (Nat.fromBitsLE (pairSnd c))

def specializationQuery (q : List Bool) : List Bool :=
  pair (pair (pair (context q) (selectedDegree q)) []) (pairSnd q)

theorem specializationQuery_FP : specializationQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair context_mem_FP selectedDegree_mem_FP) (constFn_mem_FP [])) pairSnd_mem_FP

/-- The bivariate source reader is native and may use polynomial space. -/
theorem specialize_evaluator (p : List Bool → Polynomial (Polynomial ℤ))
    (D : List Bool → ℕ) (a b : List Bool → ℤ) (hD : BinaryFn D)
    (P : SpaceFunction (PrimitivePairBits.coefficient (coefficientPolynomial p)))
    (A : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (a (pairFst c)))))
    (B : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (b (pairFst c))))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => specialize (D c) (a c) (b c) (p c))) := by
  have E := UnivariateRationalBits.evaluator (coefficientPolynomial p)
    (fun c => C (a (pairFst c))) (fun c => C (b (pairFst c)))
    (D ∘ pairFst) (hD.comp pairFst_mem_FP) P A B
  have F := E.precompose specializationQuery specializationQuery_FP
  refine F.congr (funext fun q => ?_)
  simp only [PrimitivePairBits.coefficient, specializationQuery, context, selectedDegree,
    mValue, pairFst_pair, pairSnd_pair, coefficientPolynomial, Function.comp_apply]
  rw [show Nat.fromBitsLE ([] : List Bool) = 0 from rfl]
  rw [specialize_coeff, clearCoefficient, ← Polynomial.coeff_zero_eq_eval_zero]

end LeanCanny.ETR.TubeCoordinateAnnihilator

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Algebra Polynomial

/-- Clearing a rational parameter has an explicit coefficient-mass cost. -/
theorem clearCoefficient_natAbs (D : ℕ) (a b : ℤ) (p : Polynomial ℤ)
    (hp : p.natDegree ≤ D) :
    (clearCoefficient D a b p).natAbs ≤ coefficientMass p * (max a.natAbs b.natAbs) ^ D := by
  unfold clearCoefficient
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact (coeff_natAbs_le_coefficientMass _ 0).trans
    (UnivariateRational.clear_mass D p (C a) (C b) hp _
      (by rw [coefficientMass_C]; exact le_max_left _ _)
      (by rw [coefficientMass_C]; exact le_max_right _ _))

theorem specialize_mass (D E H : ℕ) (a b : ℤ) (p : Polynomial (Polynomial ℤ))
    (hp : ∀ i, (p.coeff i).natDegree ≤ D) (he : p.natDegree ≤ E)
    (hm : ∀ i, coefficientMass (p.coeff i) ≤ H) :
    coefficientMass (specialize D a b p) ≤ (E + 1) * (H * (max a.natAbs b.natAbs) ^ D) := by
  apply coefficientMass_le _ E _ ((specialize_degree_le D a b p).trans he)
  intro i
  rw [specialize_coeff]
  exact (clearCoefficient_natAbs D a b _ (hp i)).trans (Nat.mul_le_mul_right _ (hm i))

end LeanCanny.ETR.TubeCoordinateAnnihilator
