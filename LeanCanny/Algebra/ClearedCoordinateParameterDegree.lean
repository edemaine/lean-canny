/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateCriticalBounds
public import LeanCanny.Algebra.CommonDenominatorParameterDegree
public import LeanCanny.Algebra.PurePowerParameterDegree

/-! # Retained parameter degrees on frozen critical slices

Frozen numerators of degree E and original source coefficients of degree S
give cleared relation coefficients of degree at most S+D*E. The constructed
annihilator then has coefficient degrees at most N*(bound+1)*(S+D*E), with
N and bound determined only by the free spatial arity and local degree D.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateParameterDegree
open MvPolynomial
open scoped Classical
variable {n k : ℕ} {R : Type*} [CommRing R]

theorem coordinate (q : R) (H : ℕ → Polynomial R) (offset dim E : ℕ)
    (hH : ∀ i, (H i).natDegree ≤ E) (i : ℕ) : PolynomialCoefficientDegree.Bound
      (ClearedCoordinateBlock.coordinate (Polynomial.C q) H offset dim i) E := by
  unfold ClearedCoordinateBlock.coordinate
  split_ifs
  · apply PolynomialCoefficientDegree.mono
      (PolynomialCoefficientDegree.mul (PolynomialCoefficientDegree.C (by simp : (Polynomial.C q).natDegree ≤ 0))
        (PolynomialCoefficientDegree.X _))
    exact Nat.zero_le _
  · exact PolynomialCoefficientDegree.C (hH i)

theorem specialize (D : ℕ) (q : R) (H : ℕ → Polynomial R) (offset dim S E : ℕ)
    (p : MvPolynomial (Fin n) (Polynomial R)) (hdeg : p.totalDegree ≤ D)
    (hp : PolynomialCoefficientDegree.Bound p S) (hH : ∀ i, (H i).natDegree ≤ E) :
    PolynomialCoefficientDegree.Bound (ClearedCoordinateBlock.specialize D (Polynomial.C q) H offset dim p)
      (S + D * E) :=
  PolynomialCoefficientDegree.mono
    (CommonDenominatorSpecialization.parameter_degree D q _ p S E hp (fun i => coordinate q H offset dim E hH i.val))
    (Nat.add_le_add_left (Nat.mul_le_mul_right E hdeg) S)

theorem sourceLower (D : ℕ) (q a : R) (H : ℕ → Polynomial R) (offset dim S E : ℕ)
    (low : MvPolynomial (Fin n) (Polynomial R)) (hdeg : low.totalDegree ≤ D)
    (hlow : PolynomialCoefficientDegree.Bound low S) (hH : ∀ i, (H i).natDegree ≤ E) :
    PolynomialCoefficientDegree.Bound (ClearedCoordinateBlock.lower D (Polynomial.C q) H offset dim low (Polynomial.C a))
      (S + D * E) := by
  have HF : (CoordinateBlockSpecialization.frozenPower (n := n) H offset dim D).natDegree ≤ D * E := by
    unfold CoordinateBlockSpecialization.frozenPower
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    split_ifs
    · simp
    · exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left D (hH i.val))
  apply PolynomialCoefficientDegree.add (specialize D q H offset dim S E low hdeg hlow hH)
  apply PolynomialCoefficientDegree.C
  exact Polynomial.natDegree_mul_le.trans (by
    simpa only [Polynomial.natDegree_C, Nat.zero_add] using HF.trans (Nat.le_add_left _ _))

theorem eulerLower {m : ℕ} (low : MvPolynomial (Fin (m + 1)) (Polynomial R))
    (g : Fin (m + 1) → MvPolynomial (Fin (m + 1)) (Polynomial R)) (D F : ℕ)
    (hlow : PolynomialCoefficientDegree.Bound low F) (hg : ∀ i, PolynomialCoefficientDegree.Bound (g i) F)
    (r j : Fin (m + 1)) : PolynomialCoefficientDegree.Bound (PurePowerEulerReduction.lower low g D r j) F := by
  have HO : PolynomialCoefficientDegree.Bound (PurePowerEulerReduction.objectiveLower low g D r) F := by
    unfold PurePowerEulerReduction.objectiveLower
    apply PolynomialCoefficientDegree.sub
    · simpa only [Nat.zero_add] using PolynomialCoefficientDegree.mul
        (PolynomialCoefficientDegree.C (by simp : (D : Polynomial R).natDegree ≤ 0)) hlow
    · apply PolynomialCoefficientDegree.sum
      intro i _
      simpa only [Nat.zero_add] using PolynomialCoefficientDegree.mul (PolynomialCoefficientDegree.X i) (hg i)
  unfold PurePowerEulerReduction.lower
  split_ifs
  · exact HO
  · exact hg j

theorem lower (D : ℕ) (q a : R) (H : ℕ → Polynomial R) (offset : ℕ)
    (hfit : offset + (k + 1) ≤ n + 1) (S E : ℕ) (low : MvPolynomial (Fin (n + 1)) (Polynomial R))
    (hdeg : low.totalDegree ≤ D) (hlow : PolynomialCoefficientDegree.Bound low S)
    (hH : ∀ i, (H i).natDegree ≤ E) (r j : Fin (k + 1)) :
    PolynomialCoefficientDegree.Bound (ClearedCoordinateCritical.lower D (Polynomial.C q) H offset hfit low (Polynomial.C a) r j)
      (S + D * E) := by
  apply eulerLower _ _ D _ (sourceLower D q a H offset (k + 1) S E low hdeg hlow hH)
  intro i
  exact specialize D q H offset (k + 1) S E _ ((PartialDerivativeDegree.degree_le low _).trans ((Nat.sub_le _ _).trans hdeg))
    (PolynomialCoefficientDegree.pderiv hlow _) hH

theorem coefficient (D : ℕ) (q a : R) (H : ℕ → Polynomial R) (offset : ℕ)
    (hfit : offset + (k + 1) ≤ n + 1) (S E : ℕ) (low : MvPolynomial (Fin (n + 1)) (Polynomial R))
    (hdeg : low.totalDegree ≤ D) (hlow : PolynomialCoefficientDegree.Bound low S)
    (hH : ∀ i, (H i).natDegree ≤ E) (r j : Fin (k + 1)) (t : ℕ) :
    ((ClearedCoordinateCritical.annihilator D (Polynomial.C q) H offset hfit low (Polynomial.C a) r j).coeff t).natDegree ≤
      PurePowerReductionBounds.dimension (k + 1) D * ((PurePowerReductionBounds.bound (k + 1) D + 1) * (S + D * E)) := by
  unfold ClearedCoordinateCritical.annihilator
  have HC : ((Polynomial.C a * Polynomial.C q ^ D) * (D : Polynomial R)) = Polynomial.C ((a * q ^ D) * (D : R)) := by simp
  rw [HC]
  exact PurePowerParameterDegree.coefficient _ _ _ _ (lower D q a H offset hfit S E low hdeg hlow hH r) _ _ _ _ j t

end LeanCanny.Algebra.ClearedCoordinateParameterDegree
