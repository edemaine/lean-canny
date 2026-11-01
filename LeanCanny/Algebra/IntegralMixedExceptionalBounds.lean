/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGridValue
public import LeanCanny.Algebra.IntegralMixedSquarefreeBounds

/-! # One original-spatial ceiling for all relative sweep constructions

Coordinate, selected squarefree and equation-value Gram parameter degrees
are bounded from the original spatial arity and Fermat degree. The complete
auxiliary cap also bounds the formal nilpotent coefficient extraction. No
old coefficient rank or repeated integer norm degree enters these formulas.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedExceptionalBounds
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCoordinateSquarefree FixedWidthPolynomial
open scoped Classical BigOperators

def K (a D : ℕ) := PurePowerReductionBounds.dimension a D
def E (a D : ℕ) := IntegralMixedSweepBounds.parameterCap a D
def regularCap (a D : ℕ) := (K a D + 1) * ((2 * K a D + 1) * E a D)
def boxBase (a D : ℕ) := D + a * K a D + 1
def boxWidth (a D : ℕ) := (boxBase a D).size
def valueDimension (a D : ℕ) := (a + 3) * count (a + 1) (boxWidth a D)
def valueCap (a D : ℕ) := valueDimension a D * (E a D + D)
def auxiliaryCap (a D : ℕ) := K a D + E a D + regularCap a D + valueCap a D + 1

theorem auxiliaryCap_binary {a D : List Bool → ℕ} (ha : UnaryFn a) (hD : BinaryFn D) :
    BinaryFn (fun q => auxiliaryCap (a q) (D q)) := by
  have HK := PurePowerReductionBounds.dimension_binary ha hD
  have HE := IntegralMixedSweepBounds.parameterCap_binary ha hD
  have HR := (HK.add (BinaryFn.const 1)).mul ((((BinaryFn.const 2).mul HK).add (BinaryFn.const 1)).mul HE)
  have HB := (hD.add ((BinaryFn.ofUnary ha).mul HK)).add (BinaryFn.const 1)
  have HW : UnaryFn (fun q => boxWidth (a q) (D q)) :=
    (UnaryFn.length HB.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  have HM := ((BinaryFn.ofUnary ha).add (BinaryFn.const 3)).mul
    (((BinaryFn.const 2).powUnary HW).powUnary (ha.add (UnaryFn.const 1)))
  exact (((HK.add HE).add HR).add (HM.mul (HE.add hD))).add (BinaryFn.const 1)

theorem coordinateCap_le {n : ℕ} (D : ℕ) (r : Rule n) :
    PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) D ≤ K (n + 1) D :=
  IntegralCriticalFactorCeiling.dimension_mono (by omega) (Nat.le_refl D)

theorem value_width_le {n : ℕ} (P : SpatialSource n) (r : Rule n) :
    IntegralMixedGridValue.width P r ≤ boxWidth (n + 1) P.degree := by
  apply Nat.size_le_size
  have HF : n - r.critical.offset.val + 1 ≤ n + 1 := by omega
  have HK := coordinateCap_le P.degree r
  have HM : (n - r.critical.offset.val + 1) * coordinateDegree P r ≤ (n + 1) * K (n + 1) P.degree :=
    Nat.mul_le_mul HF HK
  have HS : (n - r.critical.offset.val + 1) * (coordinateDegree P r - 1) ≤
      (n - r.critical.offset.val + 1) * coordinateDegree P r := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  change Macaulay.level (RelativeProjectiveValueGram.degrees
    (fun _ : Fin (n - r.critical.offset.val + 1) => coordinateDegree P r) P.degree) ≤ _
  simp only [Macaulay.level, RelativeProjectiveValueGram.degrees, Fin.sum_univ_succ, Fin.cases_zero,
    Fin.cases_succ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold boxBase
  omega

theorem value_dimension_le {n : ℕ} (P : SpatialSource n) (r : Rule n) :
    IntegralMixedGridValue.dimension P r ≤ valueDimension (n + 1) P.degree := by
  have HF : n - r.critical.offset.val + 1 ≤ n + 1 := by omega
  have HW := value_width_le P r
  have HC : count (n - r.critical.offset.val + 1 + 1) (IntegralMixedGridValue.width P r) ≤
      count (n + 1 + 1) (boxWidth (n + 1) P.degree) := by
    unfold count
    rw [← pow_mul, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul HW (Nat.add_le_add_right HF 1))
  exact Nat.mul_le_mul (Nat.add_le_add_right HF 3) HC

theorem value_coefficient_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : ℕ) :
    ((IntegralMixedGridValue.polynomial x hm r i).coeff k).natDegree ≤ valueCap (n + 1) P.degree :=
  (IntegralMixedGridValue.coefficient_degree x hm r i k).trans
    (Nat.mul_le_mul (value_dimension_le P r) (Nat.add_le_add_right (IntegralMixedSweepBounds.parameterDegree_le P.degree r) P.degree))

theorem regular_coefficient_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (coordinateDegree P r)) (k : ℕ) :
    ((auxiliary x hm r j i).coeff k).natDegree ≤ regularCap (n + 1) P.degree := by
  have HK := coordinateCap_le P.degree r
  have HE := IntegralMixedSweepBounds.parameterDegree_le P.degree r
  exact (IntegralMixedSquarefreeBounds.auxiliary_coefficient_degree x hm r j i k).trans
    (Nat.mul_le_mul (Nat.add_le_add_right HK 1)
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 HK) 1) HE))

theorem value_nilpotent_cap {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k N : ℕ) (hN : auxiliaryCap (n + 1) P.degree ≤ N) :
    ((IntegralMixedGridValue.polynomial x hm r i).coeff k).natDegree < N := by
  have H := value_coefficient_degree x hm r i k
  unfold auxiliaryCap at hN
  omega

end LeanCanny.Algebra.IntegralMixedExceptionalBounds
