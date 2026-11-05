/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedRegularRadiusBounds
public import LeanCanny.Encoding.BoundedRegularLowCoefficient

/-! # The actual bounded regular spatial source over the radius coefficient ring

The retained variable is the physical radius, evaluated at `2^R`. Both the
LOW polynomial and its Fermat leading scalar are constructed before this
evaluation and identified with the existing native source writer.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularRadiusLowModel
open LeanCanny.Algebra LeanCanny.Geometry Polynomial
open scoped Classical

noncomputable def coefficientForm {ι : Type*} :
    Polynomial (MvPolynomial ι ℤ) →+* MvPolynomial ι ℤ[X] :=
  Polynomial.eval₂RingHom (MvPolynomial.map (Polynomial.C : ℤ →+* ℤ[X]))
    (MvPolynomial.C Polynomial.X)

theorem coefficientForm_map_eval {ι : Type*} (p : Polynomial (MvPolynomial ι ℤ)) (t : ℤ) :
    (coefficientForm p).map (Polynomial.evalRingHom t) = p.eval (MvPolynomial.C t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, Polynomial.eval_add] using congrArg₂ (· + ·) hp hq
  | monomial k a =>
    have h : (Polynomial.evalRingHom t).comp (Polynomial.C : ℤ →+* ℤ[X]) = RingHom.id ℤ := by
      ext z
      exact Polynomial.eval_C
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    simp [coefficientForm, MvPolynomial.map_map, h, MvPolynomial.map_id]

theorem coefficientForm_coeff {ι : Type*} (p : Polynomial (MvPolynomial ι ℤ))
    (e : ι →₀ ℕ) (k : ℕ) :
    ((coefficientForm p).coeff e).coeff k = (p.coeff k).coeff e := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add, Polynomial.coeff_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] using congrArg₂ (· + ·) hp hq
  | monomial l a =>
    have hC : coefficientForm (Polynomial.C a) = MvPolynomial.map (Polynomial.C : ℤ →+* ℤ[X]) a :=
      Polynomial.eval₂_C _ _
    have hX : coefficientForm (Polynomial.X : Polynomial (MvPolynomial ι ℤ)) = MvPolynomial.C Polynomial.X :=
      Polynomial.eval₂_X _ _
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [map_mul, map_pow, hC, hX, ← MvPolynomial.C_pow]
    rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, mul_comm,
      Polynomial.C_mul_X_pow_eq_monomial]
    simp only [Polynomial.coeff_monomial]
    by_cases h : l = k <;> simp [h, Ne.symm]

theorem coefficientForm_degree {ι : Type*} (p : Polynomial (MvPolynomial ι ℤ)) (e : ι →₀ ℕ) :
    ((coefficientForm p).coeff e).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coefficientForm_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  rfl

noncomputable def leading (n D b : ℕ) : ℤ[X] :=
  Polynomial.C ((2 : ℤ) ^ BoundedRegularSource.regularizationExponent n D b 0) *
    Polynomial.X ^ BoundedRegularRadius.regularizationSlope n D

noncomputable def low {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ) :
    MvPolynomial (Fin (n + 4)) ℤ[X] :=
  coefficientForm
    (BoundedRegularRadius.powerScalar (BoundedRegularSource.regularizationExponent n D b 0)
      (BoundedRegularRadius.regularizationSlope n D) *
      (BoundedRegularRadius.powerScalar (BoundedZeroSource.perturbationExponent n D b 0)
        (BoundedRegularRadius.perturbationSlope n D) * BoundedRegularRadius.sourcePolynomial q -
        BoundedRegularRadius.powerScalar (BoundedZeroSource.penaltyExponent n D 0)
          (BoundedZeroSource.powerDegree D)) - 1)

theorem leading_degree (n D b : ℕ) :
    (leading n D b).natDegree ≤ BoundedRegularRadius.regularizationSlope n D := by
  unfold leading
  exact Polynomial.natDegree_mul_le.trans (by simp)

theorem low_coefficient_degree {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (e : Fin (n + 4) →₀ ℕ) :
    ((low q D b).coeff e).natDegree ≤ BoundedRegularRadius.parameterDegree n D := by
  unfold low
  apply (coefficientForm_degree _ e).trans
  have hprod := Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (BoundedRegularRadius.powerScalar_degree (ι := Fin (n + 4))
      (BoundedZeroSource.perturbationExponent n D b 0) (BoundedRegularRadius.perturbationSlope n D))
      (BoundedRegularRadius.sourcePolynomial_degree q))
  have hsub := (Polynomial.natDegree_sub_le _ _).trans
    (max_le (hprod.trans (Nat.le_add_right _ _))
      ((BoundedRegularRadius.powerScalar_degree (ι := Fin (n + 4))
        (BoundedZeroSource.penaltyExponent n D 0) (BoundedZeroSource.powerDegree D)).trans
        (Nat.le_add_left _ _)))
  have hfull := Polynomial.natDegree_mul_le.trans
    (Nat.add_le_add (BoundedRegularRadius.powerScalar_degree (ι := Fin (n + 4))
      (BoundedRegularSource.regularizationExponent n D b 0) (BoundedRegularRadius.regularizationSlope n D)) hsub)
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact hfull.trans_eq (by unfold BoundedRegularRadius.parameterDegree; omega)
  · simp only [Polynomial.natDegree_one]
    exact Nat.zero_le _

theorem leading_eval (n D b R : ℕ) :
    (leading n D b).eval ((2 : ℤ) ^ R) =
      IntegerRegularSource.leading (n + 3) 1 (BoundedZeroSource.powerDegree D)
        (BoundedRegularSource.sourceMassExponent n D b R) := by
  simp only [leading, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← pow_mul, ← pow_add, Nat.mul_comm R,
    ← BoundedRegularRadius.regularization_affine]
  simp only [IntegerRegularSource.leading, IntegerRegularSource.scale, mul_one]
  rfl

theorem low_map_eval {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    (low q D b).map (Polynomial.evalRingHom ((2 : ℤ) ^ R)) =
      IntegerRegularSource.lower (BoundedRegularSource.lower q D b R)
        (BoundedZeroSource.powerDegree D) (BoundedRegularSource.sourceMassExponent n D b R) := by
  rw [low, coefficientForm_map_eval]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one,
    BoundedRegularRadius.powerScalar_eval, BoundedRegularRadius.sourcePolynomial_eval]
  rw [← BoundedRegularRadius.regularization_affine,
    ← BoundedRegularRadius.perturbation_affine, ← BoundedRegularRadius.penalty_affine]
  rfl

theorem source_fields (n : List Bool → ℕ) (t : List Bool → ETR.Term)
    (radius : List Bool → ℕ) (c : List Bool) :
    (low ((t c).finitePolynomial (n c)) (t c).toData.size (t c).toData.size).map
        (Polynomial.evalRingHom ((2 : ℤ) ^ radius c)) =
      (BoundedRegularLowModularTerm.source (BoundedRegularLowCoefficient.readers n t radius) c).low ∧
    (leading (n c) (t c).toData.size (t c).toData.size).eval ((2 : ℤ) ^ radius c) =
      (BoundedRegularLowModularTerm.source (BoundedRegularLowCoefficient.readers n t radius) c).leading := by
  constructor
  · convert low_map_eval ((t c).finitePolynomial (n c)) (t c).toData.size (t c).toData.size (radius c) using 1
    simp only [BoundedRegularLowModularTerm.source, BoundedRegularLowModularTerm.low,
      BoundedRegularLowCoefficient.readers, BoundedFullWriter.controls, BoundedSourceWriter.lower,
      BoundedSourceWriter.original, BoundedSourceWriter.size, BoundedSourceWriter.degree, ETR.TermView.term_toBits]
  · convert leading_eval (n c) (t c).toData.size (t c).toData.size (radius c) using 1
    simp only [BoundedRegularLowModularTerm.source, BoundedRegularLowModularTerm.leading,
      BoundedRegularLowCoefficient.readers, BoundedFullWriter.controls, BoundedSourceWriter.leading,
      BoundedSourceWriter.size, BoundedSourceWriter.degree, ETR.TermView.term_toBits]

end LeanCanny.Encoding.BoundedRegularRadiusLowModel
