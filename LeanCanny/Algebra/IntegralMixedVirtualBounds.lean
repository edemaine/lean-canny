/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedVirtualHeight
public import LeanCanny.Algebra.IntegralMixedExpressionBounds

/-! # Original-input bounds for the actual nilpotent sweep

The virtual retained matrices have old cleared heights on the diagonal
and an integer slope on one subdiagonal. Their bounds follow from the
actual bank and the original affine syntax, including all denominator
cofactors. No coefficient bound for a relative exceptional factor is an
input to this construction.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial IntegralCoordinateBasis
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCutSource
open scoped Classical

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def scaleHeight (m G : ℕ) (r : Rule n) : ℕ := m * G + scaleBudget r.critical

noncomputable def retainedHeight (m G : ℕ) (r : Rule n) : ℕ :=
  max (retainedBudget m G r.critical + (n + 1) * scaleHeight m G r)
    (r.slope.natAbs.size + (n + 1) * scaleHeight m G r)

theorem slope_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (G C : ℕ)
    (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (i : ℕ) :
    (IntegralMixedVirtualHeight.slope x hm r i).natAbs ≤
      2 ^ (r.slope.natAbs.size + (n + 1) * scaleHeight m G r) := by
  unfold IntegralMixedVirtualHeight.slope
  split_ifs with hi hindex
  · rw [Int.natAbs_mul, pow_add]
    apply Nat.mul_le_mul (Nat.lt_size_self _).le
    have H := CommonIntegerDenominator.denominator_height
      (Finset.univ.erase (⟨i, hi⟩ : Fin (n + 1))) (data x hm r.critical).scales (scaleHeight m G r)
      (fun j _ => (familyBounds x hm r.critical G C HG HC).scale [] j)
    exact H.trans (Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_right _ ((Finset.card_le_card (Finset.erase_subset _ _)).trans_eq
        (by rw [Finset.card_univ, Fintype.card_fin]))))
  · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem matrix_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (G C : ℕ)
    (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (i : Fin (n + 1)) (u v : Fin (count (m + 1) B)) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
      (AdjoinRoot.mk (Polynomial.X ^ (2 ^ B))
        (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales
          (heights x r) i.val)) u v).natAbs ≤ 2 ^ retainedHeight m G r := by
  obtain ⟨⟨u, e⟩, rfl⟩ := (pairIndex m B).surjective u
  obtain ⟨⟨v, h⟩, rfl⟩ := (pairIndex m B).surjective v
  rw [IntegralMixedVirtualHeight.matrix]
  split_ifs with HE HH Huv
  · have H := (IntegralHistoryCriticalBits.inputs (family x hm r.critical)
      (familyBounds x hm r.critical G C HG HC)).retained [] i u v
    exact H.trans (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  · simpa only [retainedHeight, mul_one] using (slope_height x hm r G C HG HC i.val).trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  · simp only [mul_zero, Int.natAbs_zero, Nat.zero_le]
  · exact Nat.zero_le _

noncomputable def inputs (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (G C : List Bool → ℕ) (HG : ∀ q, (F.state q).bank.Bounds (G q))
    (HC : ∀ q e, ((F.spatial q).low.coeff e).natAbs ≤ 2 ^ C q) :
    IntegralOriginalCriticalBounds.Inputs (IntegralMixedVirtualSweepSource.source F I) where
  coefficientHeight := C
  retainedHeight q := retainedHeight (F.birth q) (G q) (F.rule q)
  denominatorHeight q := (F.ambient q + 1) * scaleHeight (F.birth q) (G q) (F.rule q)
  leadingHeight q := (F.spatial q).leading.natAbs.size
  coefficient q e u v := by
    change Fin (F.ambient q + 1) →₀ ℕ at e
    change Fin (count (F.birth q + 1) (F.width q)) at u v
    change (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (((F.spatial q).low.map (Int.castRingHom (IntegralMixedVirtualSweepSource.Coefficient F q))).coeff e) u v).natAbs ≤ _
    rw [MvPolynomial.coeff_map]
    exact IntegralHistoryCriticalBits.integer_entry_height _ _ _ (HC q e) u v
  retained q i u v := by
    exact matrix_height (F.state q) (F.birth_bound q) (F.rule q) (G q) (C q) (HG q) (HC q) i u v
  denominator q := by
    have H := CommonIntegerDenominator.denominator_height Finset.univ
      (data (F.state q) (F.birth_bound q) (F.rule q).critical).scales
      (scaleHeight (F.birth q) (G q) (F.rule q))
      (fun j _ => (familyBounds (F.state q) (F.birth_bound q) (F.rule q).critical (G q) (C q)
        (HG q) (HC q)).scale [] j)
    simpa only [IntegralMixedVirtualSweepSource.source, IntegralCanonicalCriticalBits.source,
      IntegralCanonicalCriticalBits.normalized, IntegralMixedVirtualSweepSource.euler,
      IntegralMixedVirtualSweepSource.original, IntegralMixedVirtualSweepSource.denominator,
      CoordinateFrozenCriticalElimination.denominator, Finset.card_univ, Fintype.card_fin] using H
  leading q := (Nat.lt_size_self _).le

noncomputable def budget (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (G C : List Bool → ℕ) (HG : ∀ q, (F.state q).bank.Bounds (G q))
    (HC : ∀ q e, ((F.spatial q).low.coeff e).natAbs ≤ 2 ^ C q) : List Bool → ℕ :=
  IntegralOriginalCriticalBounds.budget (IntegralMixedVirtualSweepSource.source F I) (inputs F I G C HG HC)

theorem coefficient_height (F : Family) (I : IntegralMixedVirtualSweepSource.Indices F)
    (G C : List Bool → ℕ) (HG : ∀ q, (F.state q).bank.Bounds (G q))
    (HC : ∀ q e, ((F.spatial q).low.coeff e).natAbs ≤ 2 ^ C q)
    (q : List Bool) (k : ℕ) (u v : Fin (count (F.birth q + 1) (F.width q))) :
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
      (AdjoinRoot.mk (Polynomial.X ^ (2 ^ F.width q))
        ((coordinate (F.state q) (F.birth_bound q) (F.rule q) (I.coordinate q)).coeff k)) u v).natAbs ≤
      2 ^ budget F I G C HG HC q := by
  let read (p : Polynomial (IntegralMixedVirtualSweepSource.Coefficient F q)) : ℕ :=
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis (p.coeff k) u v).natAbs
  have H : read ((IntegralMixedVirtualSweepSource.source F I).annihilator q) ≤
      2 ^ budget F I G C HG HC q :=
    IntegralOriginalCriticalBounds.coefficient_height (IntegralMixedVirtualSweepSource.source F I)
      (inputs F I G C HG HC) q k u v
  rw [IntegralMixedVirtualSweepSource.annihilator_eq] at H
  simpa only [read, Polynomial.coeff_map] using H

end LeanCanny.Algebra.IntegralMixedVirtualBounds
