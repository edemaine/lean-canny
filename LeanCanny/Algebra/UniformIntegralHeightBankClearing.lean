/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralHeightBank
public import LeanCanny.Algebra.CoordinateFrozenCriticalElimination

/-! # Actual frozen inputs selected from a bounded canonical height bank

A coordinate either selects an earlier canonical height or has value zero.
The common denominator and every cleared retained numerator then have
explicit bounds in the actual current-prefix basis.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix.HeightBank
open FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B m n : ℕ} {P : Prefix S (2 ^ B) m}

def selectedNumerator (H : HeightBank P) (i : Option (Fin m)) : P.carrier :=
  match i with
  | none => 0
  | some j => H.numerator j

def selectedDenominator (H : HeightBank P) (i : Option (Fin m)) : ℤ :=
  match i with
  | none => 1
  | some j => H.denominator j

theorem selected_numerator_height (H : HeightBank P) (V : ℕ) (hH : H.Bounds V)
    (i : Option (Fin m)) (r t : Fin (count m B)) :
    (Algebra.leftMulMatrix P.basis.finBasis (H.selectedNumerator i) r t).natAbs ≤ 2 ^ V := by
  cases i with
  | none => simpa only [selectedNumerator, map_zero, Matrix.zero_apply, Int.natAbs_zero] using Nat.zero_le (2 ^ V)
  | some j => exact hH.numerator j r t

theorem selected_denominator_height (H : HeightBank P) (V : ℕ) (hH : H.Bounds V)
    (i : Option (Fin m)) : (H.selectedDenominator i).natAbs ≤ 2 ^ V := by
  cases i with
  | none => exact Nat.one_le_two_pow
  | some j => exact hH.denominator j

theorem common_denominator_height (H : HeightBank P) (V : ℕ) (hH : H.Bounds V)
    (select : Fin (n + 1) → Option (Fin m)) :
    (CoordinateFrozenCriticalElimination.denominator (fun i => H.selectedDenominator (select i))).natAbs ≤
      2 ^ ((n + 1) * V) := by
  exact (CommonIntegerDenominator.denominator_height Finset.univ _ V
    (fun i _ => H.selected_denominator_height V hH (select i))).trans_eq (by simp)

theorem common_numerator_height (H : HeightBank P) (V : ℕ) (hH : H.Bounds V)
    (select : Fin (n + 1) → Option (Fin m)) (i : Fin (n + 1)) (r t : Fin (count m B)) :
    (Algebra.leftMulMatrix P.basis.finBasis
      (CoordinateFrozenCriticalElimination.numerators (fun i => H.selectedDenominator (select i))
        (fun i => H.selectedNumerator (select i)) i.val) r t).natAbs ≤ 2 ^ ((n + 2) * V) := by
  rw [CoordinateFrozenCriticalElimination.numerators, dite_eq_left i.isLt]
  have HE := CommonIntegerDenominator.numerator_height P.basis.finBasis Finset.univ
    (fun i => H.selectedDenominator (select i)) (fun i => H.selectedNumerator (select i)) V V
    (fun j _ => H.selected_denominator_height V hH (select j)) i
    (H.selected_numerator_height V hH (select i)) r t
  simpa only [Finset.card_univ, Fintype.card_fin, show V + (n + 1) * V = (n + 2) * V by ring] using HE

end LeanCanny.Algebra.UniformIntegralPrefix.HeightBank
