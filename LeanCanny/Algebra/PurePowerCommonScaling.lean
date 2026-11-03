/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PurePowerRelativeAnnihilator
/-! # Common scaling of the actual reduction rows and cleared coordinate polynomial

A common nonzero factor in every critical row does not change its roots.
The displayed integral annihilator scales by an explicit power; it is not
identified with an unrelated norm or assumed to have a unit leading term.
-/
@[expose] public section
namespace LeanCanny.Algebra.PurePowerCommonScaling
open MvPolynomial Matrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n B : ℕ} {R : Type*} [CommRing R]

theorem reduction (fallback : Fin n) (d : Fin n→ℕ)
    (low : Fin n→MvPolynomial (Fin n) R) (c s : R) (bound : ℕ) :
    PurePowerReductionMatrix.matrix (B:=B) fallback d (fun i=>MvPolynomial.C s*low i) (s*c) bound=
      s • PurePowerReductionMatrix.matrix fallback d low c bound :=by
  have HS (p : MvPolynomial (Fin n) R) (e : Fin n→₀ℕ) (i : Fin n) (k : ℕ) :
      MonicMonomialReduction.step (MvPolynomial.C s*p) e i k=
        MvPolynomial.C s*MonicMonomialReduction.step p e i k:=by
    unfold MonicMonomialReduction.step
    ring
  funext i j
  simp only [PurePowerReductionMatrix.matrix,Matrix.smul_apply,smul_eq_mul]
  split_ifs
  · rfl
  · ring
  · rw [HS,MvPolynomial.coeff_C_mul]
  · ring

theorem action (fallback : Fin n) (d : Fin n→ℕ)
    (low : Fin n→MvPolynomial (Fin n) R) (c s : R) (bound : ℕ)
    (hgrid : PurePowerReductionMatrix.gridBound d+1≤bound) (hbound : bound<2^B) (j : Fin n) :
    PurePowerRelativeAnnihilator.actionMatrix fallback d (fun i=>MvPolynomial.C s*low i) (s*c) bound hgrid hbound j=
      s^(bound+1) • PurePowerRelativeAnnihilator.actionMatrix fallback d low c bound hgrid hbound j :=by
  unfold PurePowerRelativeAnnihilator.actionMatrix
  rw [reduction]
  ext i k
  simp only [GradedReductionAnnihilator.paddedMatrix,smul_pow,Matrix.smul_apply,smul_eq_mul]
  split_ifs <;> ring

theorem scaled_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (c s : R) (e : ℕ) :
    ScaledGradedReductionAnnihilator.polynomial (s^e • M) (s*c) e=
      Polynomial.C (s^(e*Fintype.card ι))*ScaledGradedReductionAnnihilator.polynomial M c e :=by
  let q : Polynomial R:=Polynomial.C ((s*c)^e)*Polynomial.X
  let q₀ : Polynomial R:=Polynomial.C (c^e)*Polynomial.X
  have HM : (Matrix.charmatrix (s^e • M)).map (Polynomial.compRingHom q)=
      Polynomial.C (s^e) • (Matrix.charmatrix M).map (Polynomial.compRingHom q₀) :=by
    funext i j
    simp only [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Polynomial.coe_compRingHom_apply]
    by_cases hij : i=j
    · subst j
      simp only [Matrix.charmatrix_apply_eq,Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp,
        Matrix.smul_apply,smul_eq_mul]
      dsimp only [q,q₀]
      simp only [mul_pow,Polynomial.C_mul]
      ring
    · simp only [Matrix.charmatrix_apply_ne _ _ _ hij,Polynomial.neg_comp,Polynomial.C_comp,
        Matrix.smul_apply,smul_eq_mul,Polynomial.C_mul,Polynomial.mul_comp]
      ring

  unfold ScaledGradedReductionAnnihilator.polynomial Matrix.charpoly
  change (Polynomial.compRingHom q) (Matrix.charmatrix (s^e • M)).det=
    Polynomial.C (s^(e*Fintype.card ι))*(Polynomial.compRingHom q₀) (Matrix.charmatrix M).det
  rw [RingHom.map_det,RingHom.mapMatrix_apply,HM,Matrix.det_smul]
  rw [←Polynomial.C_pow,←pow_mul]
  congr 1
  simpa only [RingHom.mapMatrix_apply] using (RingHom.map_det (Polynomial.compRingHom q₀) (Matrix.charmatrix M)).symm

theorem polynomial (fallback : Fin n) (d : Fin n→ℕ)
    (low : Fin n→MvPolynomial (Fin n) R) (c s : R) (bound : ℕ)
    (hgrid : PurePowerReductionMatrix.gridBound d+1≤bound) (hbound : bound<2^B) (j : Fin n) :
    PurePowerRelativeAnnihilator.polynomial fallback d (fun i=>MvPolynomial.C s*low i) (s*c) bound hgrid hbound j=
      Polynomial.C (s^((bound+1)*FixedWidthPolynomial.count n B))*
        PurePowerRelativeAnnihilator.polynomial fallback d low c bound hgrid hbound j :=by
  unfold PurePowerRelativeAnnihilator.polynomial
  rw [action,scaled_polynomial]
  simp only [Fintype.card_fin]

end LeanCanny.Algebra.PurePowerCommonScaling
