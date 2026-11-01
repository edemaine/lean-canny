/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralRelativeCharacteristicBounds
public import LeanCanny.Algebra.RelativeValueSystemMap

/-! # Multiplication-matrix heights for actual homogeneous Macaulay Grams

Homogenization and monomial shifts select one original coefficient.
Padding rows cost only the identity. A Gram entry is an explicit sum of
products, whose rank and row-count costs are included before the actual
relative determinant bound is applied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMacaulayGramBounds
open LeanCanny.Encoding LeanCanny.Computation MvPolynomial
open scoped Classical BigOperators
variable {A : Type*} [CommRing A] {M : ℕ}

theorem homogeneous_height {n : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (p : MvPolynomial (Fin n) A) (d H : ℕ)
    (hp : ∀ e r t, (Algebra.leftMulMatrix b (p.coeff e) r t).natAbs ≤ 2 ^ H)
    (e : Fin (n + 1) →₀ ℕ) (r t : Fin M) :
    (Algebra.leftMulMatrix b ((RelativeValueSystemMap.homogeneousTest p d).coeff e) r t).natAbs ≤ 2 ^ H := by
  by_cases HZ : (RelativeValueSystemMap.homogeneousTest p d).coeff e = 0
  · rw [HZ, map_zero, Matrix.zero_apply, Int.natAbs_zero]
    exact Nat.zero_le _
  · obtain ⟨w, hw, _⟩ := coeff_rename_ne_zero (AffineFiniteCoordinates.layout n) _ e HZ
    rw [← hw, RelativeValueSystemMap.homogeneousTest,
      coeff_rename_mapDomain _ (AffineFiniteCoordinates.layout n).injective, WeightedHomogenization.coefficient]
    split_ifs
    · exact hp _ r t
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _

theorem macaulay_height {n : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (p : Fin n → MvPolynomial (Fin n) A) (d : Fin n → ℕ) (W H : ℕ)
    (hp : ∀ i e r t, (Algebra.leftMulMatrix b ((p i).coeff e) r t).natAbs ≤ 2 ^ H)
    (a : MacaulayFullBox.Row n W) (c : MacaulayFullBox.Column n W) (r t : Fin M) :
    (Algebra.leftMulMatrix b (MacaulayFullBox.matrix p d W a c) r t).natAbs ≤ 2 ^ H := by
  rcases a with ⟨i, a⟩ | a
  · change (Algebra.leftMulMatrix b (if _ then _ else 0) r t).natAbs ≤ _
    split_ifs
    · rw [coeff_monomial_mul']
      split_ifs
      · rw [one_mul]
        exact hp i _ r t
      · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
        exact Nat.zero_le _
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _
  · change (Algebra.leftMulMatrix b (if _ then if _ then 1 else 0 else 0) r t).natAbs ≤ _
    split_ifs
    · rw [map_one, Matrix.one_apply]
      split_ifs
      · exact Nat.one_le_two_pow
      · exact Nat.zero_le _
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _
    · rw [map_zero, Matrix.zero_apply, Int.natAbs_zero]
      exact Nat.zero_le _

def gramHeight (rows rank H : ℕ) : ℕ := H + H + rank.size + rows.size

theorem gramHeight_binary {rows rank H : List Bool → ℕ}
    (hrows : BinaryFn rows) (hrank : BinaryFn rank) (hH : BinaryFn H) :
    BinaryFn (fun q => gramHeight (rows q) (rank q) (H q)) := ((hH.add hH).add hrank.size).add hrows.size

theorem gram_height {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : Module.Basis (Fin M) ℤ A) (T : Matrix ι κ A) (H : ℕ)
    (hT : ∀ i j r t, (Algebra.leftMulMatrix b (T i j) r t).natAbs ≤ 2 ^ H)
    (i j : κ) (r t : Fin M) :
    (Algebra.leftMulMatrix b (ProjectiveGramEliminant.gram T i j) r t).natAbs ≤
      2 ^ gramHeight (Fintype.card ι) M H := by
  rw [ProjectiveGramEliminant.gram, Matrix.mul_apply, map_sum, Matrix.sum_apply]
  calc
    _ ≤ ∑ k : ι, (Algebra.leftMulMatrix b (T.transpose i k * T k j) r t).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k : ι, 2 ^ (H + H + M.size) := by
      apply Finset.sum_le_sum
      intro k _
      rw [map_mul]
      exact IntegralParameterMatrixBounds.mul_height _ _ H H (hT k i) (hT k j) r t
    _ = Fintype.card ι * 2 ^ (H + H + M.size) := by simp
    _ ≤ 2 ^ (Fintype.card ι).size * 2 ^ (H + H + M.size) := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := by rw [← pow_add]; unfold gramHeight; congr 1; omega

theorem macaulay_row_count (n W : ℕ) :
    Fintype.card (MacaulayFullBox.Row n W) = (n + 1) * FixedWidthPolynomial.count n W := by
  simp only [MacaulayFullBox.Row, MacaulayFullBox.Column, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

theorem determinant_height {n : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (p : Fin n → MvPolynomial (Fin n) A) (d : Fin n → ℕ) (W H : ℕ)
    (hp : ∀ i e r t, (Algebra.leftMulMatrix b ((p i).coeff e) r t).natAbs ≤ 2 ^ H)
    (r t : Fin M) :
    (Algebra.leftMulMatrix b (ProjectiveGramEliminant.gram (MacaulayFullBox.matrix p d W)).det r t).natAbs ≤
      2 ^ IntegralRelativeCharacteristicBounds.determinantHeight (FixedWidthPolynomial.count n W) M
        (gramHeight ((n + 1) * FixedWidthPolynomial.count n W) M H) := by
  have HG := gram_height b (MacaulayFullBox.matrix p d W) H (macaulay_height b p d W H hp)
  have HD := IntegralRelativeCharacteristicBounds.determinant_height b
    (ProjectiveGramEliminant.gram (MacaulayFullBox.matrix p d W))
    (gramHeight (Fintype.card (MacaulayFullBox.Row n W)) M H) HG r t
  simpa only [macaulay_row_count, MacaulayFullBox.Column, Fintype.card_fin] using HD

end LeanCanny.Algebra.IntegralMacaulayGramBounds
