/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientRelativeLeadingNormalization
public import LeanCanny.Algebra.ParameterMatrixPolynomialBounds

/-! # Parameter bounds for actual relative leading normalization

The fixed characteristic-coefficient index may be arbitrary. The resulting
coefficient multiplication matrices have degree and mass bounds linear in
the input degree and height. No inverse matrix or reduced algebra is needed.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientRelativeNormalizationMatrixBounds
open Polynomial CoefficientRelativeLeadingNormalization ParameterMatrixMassBounds
  ParameterMatrixPolynomialBounds
open scoped Classical

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι]

noncomputable def inverseMatrixAt (b : Module.Basis ι R A) (p : A[X]) (d τ : ℕ) :=
  Polynomial.aeval (Algebra.leftMulMatrix b (p.coeff d))
    (IntegralParameterInverse.inverseAt (Algebra.leftMulMatrix b (p.coeff d)).charpoly τ)

theorem inverseMatrixAt_eq (b : Module.Basis ι R A) (p : A[X]) (d τ : ℕ) :
    inverseMatrixAt b p d τ = Algebra.leftMulMatrix b (inverseValueAt b (p.coeff d) τ) := by
  unfold inverseMatrixAt inverseValueAt
  change _ = Algebra.leftMulMatrix b (Polynomial.aeval (p.coeff d) _)
  rw [← Polynomial.aeval_algHom_apply]

theorem coefficient_eq (b : Module.Basis ι R A) (p : A[X]) (d τ k : ℕ) :
    (normalizeAt b p d τ).coeff k =
      if k = d then algebraMap R A (denominatorAt b (p.coeff d) τ)
      else inverseValueAt b (p.coeff d) τ * p.coeff k := by
  by_cases H : k = d
  · subst k
    rw [ite_eq_left rfl, coefficient]
  · have H' : d ≠ k := Ne.symm H
    simp only [normalizeAt, coeff_add, coeff_monomial, H', ite_false,
      coeff_C_mul, coeff_sub, sub_zero, zero_add, ite_eq_right H]

theorem matrix_eq (b : Module.Basis ι R A) (p : A[X]) (d τ k : ℕ) :
    Algebra.leftMulMatrix b ((normalizeAt b p d τ).coeff k) =
      if k = d then denominatorAt b (p.coeff d) τ • (1 : Matrix ι ι R)
      else inverseMatrixAt b p d τ * Algebra.leftMulMatrix b (p.coeff k) := by
  rw [coefficient_eq]
  split_ifs
  · rw [AlgHom.commutes]
    simp only [Algebra.algebraMap_eq_smul_one]
  · rw [map_mul, ← inverseMatrixAt_eq]

def normalizationBudget (n H : ℕ) :=
  evaluationBudget n n H (characteristicBudget n H) + H + n.size

theorem normalizationBudget_binary {n H : List Bool → ℕ}
    (hn : BinaryFn n) (hH : BinaryFn H) :
    BinaryFn (fun q => normalizationBudget (n q) (H q)) :=
  ((evaluationBudget_binary hn hn hH (characteristicBudget_binary hn hH)).add hH).add hn.size

theorem normalizationBudget_affine (n H : ℕ) :
    normalizationBudget n H = (2 * n + 1) * H +
      (n + (2 * n + 1) * n.size + (n + 1).size) := by
  unfold normalizationBudget evaluationBudget characteristicBudget
  ring

section Parameter
variable {B : Type*} [CommRing B] [Algebra ℤ[X] B]

theorem inverseMatrixAt_mass (b : Module.Basis ι ℤ[X] B) (p : B[X]) (d τ H : ℕ)
    (hp : ∀ k i j, coefficientMass (Algebra.leftMulMatrix b (p.coeff k) i j) ≤ 2 ^ H)
    (i j : ι) :
    coefficientMass (inverseMatrixAt b p d τ i j) ≤
      2 ^ evaluationBudget (Fintype.card ι) (Fintype.card ι) H
        (characteristicBudget (Fintype.card ι) H) := by
  apply aeval_mass
  · exact (inverseAt_degree _ _).trans (by rw [Matrix.charpoly_natDegree_eq_dim])
  · exact hp d
  · exact inverseAt_coefficient_mass _ τ _ (charpoly_coefficient_mass _ H (hp d))

theorem normalized_coefficient_mass (b : Module.Basis ι ℤ[X] B) (p : B[X]) (d τ H : ℕ)
    (hp : ∀ k i j, coefficientMass (Algebra.leftMulMatrix b (p.coeff k) i j) ≤ 2 ^ H)
    (k : ℕ) (i j : ι) :
    coefficientMass (Algebra.leftMulMatrix b ((normalizeAt b p d τ).coeff k) i j) ≤
      2 ^ normalizationBudget (Fintype.card ι) H := by
  rw [matrix_eq]
  split_ifs
  · simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      apply (charpoly_coefficient_mass _ H (hp d) τ).trans
      apply Nat.pow_le_pow_right (by decide)
      unfold normalizationBudget evaluationBudget
      omega
    · simp
  · exact mul_mass _ _ _ H (inverseMatrixAt_mass b p d τ H hp) (hp k) i j

theorem inverseMatrixAt_degree (b : Module.Basis ι ℤ[X] B) (p : B[X]) (d τ E : ℕ)
    (hp : ∀ k, RelativeMatrixDegree.Bound (Algebra.leftMulMatrix b (p.coeff k)) E)
    (i j : ι) :
    (inverseMatrixAt b p d τ i j).natDegree ≤ 2 * Fintype.card ι * E := by
  unfold inverseMatrixAt
  have h := aeval_degree (Algebra.leftMulMatrix b (p.coeff d))
    (IntegralParameterInverse.inverseAt (Algebra.leftMulMatrix b (p.coeff d)).charpoly τ)
    (Fintype.card ι) E (Fintype.card ι * E)
    ((inverseAt_degree _ _).trans (by rw [Matrix.charpoly_natDegree_eq_dim])) (hp d)
    (inverseAt_coefficient_degree _ τ _ (RelativeMatrixDegree.charpoly_coefficient (hp d))) i j
  convert h using 1
  ring

theorem normalized_coefficient_degree (b : Module.Basis ι ℤ[X] B) (p : B[X]) (d τ E : ℕ)
    (hp : ∀ k, RelativeMatrixDegree.Bound (Algebra.leftMulMatrix b (p.coeff k)) E)
    (k : ℕ) (i j : ι) :
    (Algebra.leftMulMatrix b ((normalizeAt b p d τ).coeff k) i j).natDegree ≤
      (2 * Fintype.card ι + 1) * E := by
  rw [matrix_eq]
  split_ifs
  · simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact (RelativeMatrixDegree.charpoly_coefficient (hp d) τ).trans
        (Nat.mul_le_mul_right E (by omega))
    · simp
  · have h := RelativeMatrixDegree.mul (inverseMatrixAt_degree b p d τ E hp) (hp k) i j
    convert h using 1
    ring

end Parameter

def birthBudget (N m H : ℕ) :=
  stepBudget N m (normalizationBudget (N ^ m) H)

theorem birthBudget_binary {N m H : List Bool → ℕ}
    (hN : BinaryFn N) (hm : UnaryFn m) (hH : BinaryFn H) :
    BinaryFn (fun q => birthBudget (N q) (m q) (H q)) :=
  stepBudget_binary hN hm (normalizationBudget_binary (hN.powUnary hm) hH)

theorem birthBudget_affine (N m H : ℕ) :
    birthBudget N m H = N * (2 * N ^ m + 1) * H +
      N * (N ^ m + (2 * N ^ m + 2) * (N ^ m).size + (N ^ m + 1).size) := by
  unfold birthBudget stepBudget
  rw [normalizationBudget_affine]
  ring

theorem normalized_step_root_bounds {B : Type*} [CommRing B] [Nontrivial B]
    [Algebra ℤ[X] B] {m N : ℕ} (b : CoefficientCoordinateBasis ℤ[X] B m N)
    (p : B[X]) (d τ H E : ℕ)
    (hMass : ∀ k i j, coefficientMass (Algebra.leftMulMatrix b.basis (p.coeff k) i j) ≤ 2 ^ H)
    (hDegree : ∀ k, RelativeMatrixDegree.Bound (Algebra.leftMulMatrix b.basis (p.coeff k)) E)
    (i j : Fin (m + 1) → Fin N) :
    let M := Algebra.leftMulMatrix (b.paddedStep (normalizeAt b.basis p d τ) d).basis
      (AdjoinRoot.root _)
    coefficientMass (M i j) ≤ 2 ^ birthBudget N m H ∧
      (M i j).natDegree ≤ N * ((2 * N ^ m + 1) * E) := by
  constructor
  · have h := padded_root_mass b (normalizeAt b.basis p d τ) d
      (normalizationBudget (Fintype.card (Fin m → Fin N)) H)
      (normalized_coefficient_mass b.basis p d τ H hMass) i j
    simpa only [Fintype.card_fun, Fintype.card_fin, birthBudget, stepBudget] using h
  · have h := padded_root_degree b (normalizeAt b.basis p d τ) d
      ((2 * Fintype.card (Fin m → Fin N) + 1) * E)
      (normalized_coefficient_degree b.basis p d τ E hDegree) i j
    simpa only [Fintype.card_fun, Fintype.card_fin] using h

end LeanCanny.Algebra.CoefficientRelativeNormalizationMatrixBounds
