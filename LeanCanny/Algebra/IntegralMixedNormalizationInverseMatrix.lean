/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationModularTop
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeInverse
public import LeanCanny.Algebra.IntegralMixedNormalizationNativeTopPower
public import LeanCanny.Algebra.MatrixPolynomialEntryCorrect
/-! # The streamed inverse polynomial is the literal cut normalization matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def inverseMatrix (F : Family) (key : List Bool) := IntegralMixedCutProduct.inverse F key

theorem inverse_matrix_sum (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin (matrixDimension P F q)) :
    (inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) i j : ZMod (modulus P q)) =
      ∑ k ∈ Finset.range (matrixDimension P F q + 1),
        (((IntegralParameterInverse.inverse (top F (IntegralMixedVirtualTaskBits.saved P q)).charpoly).coeff k : ℤ) :
          ZMod (modulus P q)) * (modularTop P F q ^ k) i j := by
  let M := top F (IntegralMixedVirtualTaskBits.saved P q)
  let p := IntegralParameterInverse.inverse M.charpoly
  have HD : p.natDegree < matrixDimension P F q + 1 := by
    have H := IntegralParameterInverse.natDegree_inverse_le M.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at H
    exact Nat.lt_succ_of_le H
  have HE := MatrixPolynomialEntryBits.polynomial_entry p M (matrixDimension P F q + 1) HD i j
  have HC := congrArg (fun z : ℤ => (z : ZMod (modulus P q))) HE
  simp only [Int.cast_sum, Int.cast_mul] at HC
  have HI : inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) = p.eval₂ (Matrix.scalar _) M :=
    IntegralMixedCutProduct.inverse_eq F (IntegralMixedVirtualTaskBits.saved P q)
  rw [HI]
  refine HC.trans ?_
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  change ((M ^ k) i j : ZMod (modulus P q)) = ((M.map (Int.castRingHom (ZMod (modulus P q)))) ^ k) i j
  rw [← Matrix.map_pow]
  rfl

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
