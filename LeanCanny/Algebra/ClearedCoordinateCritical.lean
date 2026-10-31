/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateBlock
public import LeanCanny.Algebra.PurePowerEulerReduction

/-! # Integral relative annihilators on frozen coordinate slices

Source and gradient rows use the original total-degree clearing allowance.
Their leading coefficient is the same constant a*D*q^D. Euler elimination
and the concrete reduction matrix therefore give relative coordinate
annihilators without introducing rational coefficient inverses.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateCritical
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n k B : ℕ} {R : Type*} [CommRing R]

def freeIndex (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1) (j : Fin (k + 1)) : Fin (n + 1) :=
  ⟨offset + j.val, by omega⟩

noncomputable def gradientLower (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ)
    (hfit : offset + (k + 1) ≤ n + 1) (low : MvPolynomial (Fin (n + 1)) R) (j : Fin (k + 1)) :
    MvPolynomial (Fin (k + 1)) R :=
  ClearedCoordinateBlock.specialize D q H offset (k + 1) (pderiv (freeIndex offset hfit j) low)

theorem free_coordinate (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (j : Fin (k + 1)) :
    ClearedCoordinateBlock.coordinate q H offset (k + 1) (freeIndex offset hfit j).val = C q * X j := by
  have HI : offset ≤ (freeIndex offset hfit j).val ∧ (freeIndex offset hfit j).val < offset + (k + 1) := by
    dsimp [freeIndex]
    omega
  rw [ClearedCoordinateBlock.coordinate, dite_eq_left HI]
  congr 2
  apply Fin.ext
  simp only [freeIndex, Nat.add_sub_cancel_left]

theorem gradient_eq (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (j : Fin (k + 1)) :
    ClearedCoordinateBlock.specialize D q H offset (k + 1)
      (pderiv (freeIndex offset hfit j) (FermatCriticalHomogenization.polynomial low a D)) =
      PurePowerEulerReduction.gradient (a * q ^ D) D (gradientLower D q H offset hfit low) j := by
  rw [FermatCriticalHomogenization.pderiv_polynomial, map_add]
  change gradientLower D q H offset hfit low j + _ = _
  rw [ClearedCoordinateBlock.specialize, CommonDenominatorSpecialization.C_mul,
    CommonDenominatorSpecialization.X_pow, free_coordinate q H offset hfit j]
  have HQ : q ^ (D - (D - 1)) * q ^ (D - 1) = q ^ D := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.sub_le D 1)]
  have HL : C (a * (D : R)) * (C (q ^ (D - (D - 1))) * (C q * X j) ^ (D - 1)) =
      (C ((a * q ^ D) * (D : R)) * X j ^ (D - 1) : MvPolynomial (Fin (k + 1)) R) := by
    rw [mul_pow, ← map_pow]
    calc
      _ = C ((a * (D : R)) * (q ^ (D - (D - 1)) * q ^ (D - 1))) * X j ^ (D - 1) := by
        simp only [map_mul]
        ring
      _ = _ := by rw [HQ]; congr 2; ring
  rw [HL, PurePowerEulerReduction.gradient]
  exact add_comm _ _

theorem gradient_degree (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (hD : 2 ≤ D) (hlow : low.totalDegree < D) (j : Fin (k + 1)) :
    (gradientLower D q H offset hfit low j).totalDegree < D - 1 := by
  exact (ClearedCoordinateBlock.degree D q H offset (k + 1) _).trans_lt
    ((PartialDerivativeDegree.degree_le low _).trans_lt (by omega))

noncomputable def lower (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (r : Fin (k + 1)) (j : Fin (k + 1)) :
    MvPolynomial (Fin (k + 1)) R :=
  PurePowerEulerReduction.lower (ClearedCoordinateBlock.lower D q H offset (k + 1) low a)
    (gradientLower D q H offset hfit low) D r j

theorem lower_degree (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (hD : 2 ≤ D) (hlow : low.totalDegree < D)
    (r j : Fin (k + 1)) :
    (lower D q H offset hfit low a r j).totalDegree < FermatCoordinateCriticalReduction.degrees r D j :=
  PurePowerEulerReduction.lower_degree _ _ D hD (ClearedCoordinateBlock.lower_degree D q H offset (k + 1) low a hlow)
    (gradient_degree D q H offset hfit low hD hlow) r j

theorem coordinate_annihilator_root [Nontrivial R] {K : Type*} [Field K] (φ : R →+* K)
    (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ) (hfit : offset + (k + 1) ≤ n + 1)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (hD : 2 ≤ D) (hlow : low.totalDegree < D)
    (hq : φ q ≠ 0) (r : Fin (k + 1)) (bound : ℕ)
    (hgrid : PurePowerReductionMatrix.gridBound (FermatCoordinateCriticalReduction.degrees r D) + 1 ≤ bound)
    (hbound : bound < 2 ^ B) (x : Fin (k + 1) → K)
    (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ (ClearedCoordinateBlock.point φ q H offset x) = 0)
    (hg : ∀ j, j ≠ r → (pderiv (freeIndex offset hfit j) (FermatCriticalHomogenization.polynomial low a D)).eval₂
      φ (ClearedCoordinateBlock.point φ q H offset x) = 0) (j : Fin (k + 1)) :
    (PurePowerRelativeAnnihilator.polynomial r (FermatCoordinateCriticalReduction.degrees r D)
      (lower D q H offset hfit low a r) ((a * q ^ D) * (D : R)) bound hgrid hbound j).eval₂ φ (x j) = 0 := by
  have HD : ∀ i, 0 < FermatCoordinateCriticalReduction.degrees r D i := by
    intro i
    unfold FermatCoordinateCriticalReduction.degrees
    split_ifs <;> omega
  have HPdegree := FermatCriticalHomogenization.polynomial_degree low a D hlow
  have HP : (FermatCriticalHomogenization.polynomial (ClearedCoordinateBlock.lower D q H offset (k + 1) low a)
      (a * q ^ D) D).eval₂ φ x = 0 := by
    rw [← ClearedCoordinateBlock.source D q H offset low a hfit,
      ClearedCoordinateBlock.eval φ D q H offset _ HPdegree hq x, hp, mul_zero]
  have HG : ∀ i, i ≠ r → (PurePowerEulerReduction.gradient (a * q ^ D) D
      (gradientLower D q H offset hfit low) i).eval₂ φ x = 0 := by
    intro i hi
    have HGdegree : (pderiv (freeIndex offset hfit i) (FermatCriticalHomogenization.polynomial low a D)).totalDegree ≤ D :=
      (PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans HPdegree)
    rw [← gradient_eq D q H offset hfit low a i,
      ClearedCoordinateBlock.eval φ D q H offset _ HGdegree hq x, hg i hi, mul_zero]
  exact PurePowerRelativeAnnihilator.root φ r _ HD _ (lower_degree D q H offset hfit low a hD hlow r)
    _ bound hgrid hbound j x (PurePowerEulerReduction.relations_root φ _ _ (a * q ^ D) D (by omega) r x HP HG)

end LeanCanny.Algebra.ClearedCoordinateCritical
