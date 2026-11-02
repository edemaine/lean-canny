/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutMatrix
public import LeanCanny.Algebra.IntegralNilpotentParameter

/-! # Literal relative-factor matrices through one bounded nilpotent

Every one of the three constructed factors has sweep degree STRICTLY
below the one initial cap. A coefficient matrix is therefore an actual
submatrix of the factor's value in the formal nilpotent extension.
Out-of-range coefficients stay zero instead of wrapping their indices.
The extension has rank `count (m+1) B`; no full absolute norm is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutNilpotent
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts IntegralMixedCutMatrix
open IntegralMixedExceptionalBounds IntegralCoordinateBasis FixedWidthPolynomial Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem factor_degree_lt (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) :
    (factor x hm r c).natDegree < auxiliaryCap (n + 1) P.degree := by
  cases c with
  | coordinate j k =>
    have H : (IntegralMixedCoordinateTrailing.factor x hm r j k).natDegree ≤ E (n + 1) P.degree :=
      IntegralMixedSweepBounds.factor_degree x hm r j k
    change (IntegralMixedCoordinateTrailing.factor x hm r j k).natDegree < _
    unfold auxiliaryCap
    omega
  | value i k =>
    have H := IntegralMixedValueTrailing.factor_degree x hm r i k
    change (IntegralMixedValueTrailing.factor x hm r i k).natDegree < _
    unfold auxiliaryCap
    omega
  | squarefree j k =>
    have HK := coordinateCap_le P.degree r
    have Hη := IntegralMixedSweepBounds.parameterDegree_le P.degree r
    have HC := (IntegralMixedSquarefreeBounds.exceptional_degree x hm r j k).trans
      (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 2 HK) 1) Hη)
    have HM : (2 * K (n + 1) P.degree + 1) * E (n + 1) P.degree ≤ regularCap (n + 1) P.degree :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have HB : (IntegralMixedCoordinateSquarefree.exceptional x hm r j k).natDegree ≤ regularCap (n + 1) P.degree :=
      HC.trans HM
    change (IntegralMixedCoordinateSquarefree.exceptional x hm r j k).natDegree < _
    unfold auxiliaryCap
    omega
  | limitCoordinate j c =>
    have HC := IntegralMixedLimitCoordinate.factor_degree x hm r j c
    have HI : c.val < PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree + 1 := c.isLt
    have HK := coordinateCap_le P.degree r
    change (IntegralMixedLimitCoordinate.factor x hm r j c).natDegree < _
    unfold auxiliaryCap
    omega

noncomputable def basis (x : State P S B m ι) :=
  x.sampler.scalarPrefix.basis.step (X ^ (2 ^ B)) (monic_X_pow _) (natDegree_X_pow _)

noncomputable def value (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r) :=
  AdjoinRoot.mk (X ^ (2 ^ B)) (factor x hm r c)

theorem coefficient (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r)
    (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (k : Fin (2 ^ B)) (i j : Fin (count m B)) :
    Algebra.leftMulMatrix (basis x).finBasis (value x hm r c)
      (pairIndex m B (i, k)) (pairIndex m B (j, 0)) = coefficientMatrix x hm r c k.val i j := by
  exact IntegralNilpotentParameter.fixedWidth_coefficient x.sampler.scalarPrefix.basis
    (factor x hm r c) ((factor_degree_lt x hm r c).trans_le hcap) i j k

theorem coefficient_outside (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r)
    (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B) (k : ℕ) (hk : 2 ^ B ≤ k) :
    coefficientMatrix x hm r c k = 0 := by
  unfold coefficientMatrix
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    (((factor_degree_lt x hm r c).trans_le hcap).trans_le hk), map_zero]

theorem pairIndex_value (i : Fin (count m B)) (k : Fin (2 ^ B)) :
    (pairIndex m B (i, k)).val = k.val + 2 ^ B * i.val := rfl

end LeanCanny.Algebra.IntegralMixedCutNilpotent
