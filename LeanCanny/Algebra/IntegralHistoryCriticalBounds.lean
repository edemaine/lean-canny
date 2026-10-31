/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryCriticalSource
public import LeanCanny.Algebra.IntegralOriginalCriticalFactorBounds
public import LeanCanny.Algebra.UniformIntegralHeightBankClearing

/-! # Critical coefficient budgets from actual history inputs

Integer source coefficients, old numerator matrices, integer scales, and
the source leading integer bound the constructed critical polynomial.
Common-denominator clearing is included in these derived budgets.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Bounds (F : Family) where
  coefficientHeight : List Bool → ℕ
  retainedHeight : List Bool → ℕ
  scaleHeight : List Bool → ℕ
  leadingHeight : List Bool → ℕ
  coefficient : ∀ c e, ((F.data c).low.coeff e).natAbs ≤ 2 ^ coefficientHeight c
  retained : ∀ c i r t,
    (Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis ((F.data c).heights i) r t).natAbs ≤ 2 ^ retainedHeight c
  scale : ∀ c i, ((F.data c).scales i).natAbs ≤ 2 ^ scaleHeight c
  leading : ∀ c, ((F.data c).leading).natAbs ≤ 2 ^ leadingHeight c

theorem integer_entry_height {A : Type*} [CommRing A] {M : ℕ} (b : Module.Basis (Fin M) ℤ A)
    (z : ℤ) (C : ℕ) (hz : z.natAbs ≤ 2 ^ C) (r t : Fin M) :
    (Algebra.leftMulMatrix b (z : A) r t).natAbs ≤ 2 ^ C := by
  rw [map_intCast, Matrix.intCast_apply]
  split_ifs
  · simpa only [Int.cast_id] using hz
  · exact Nat.zero_le _

noncomputable def inputs (F : Family) (H : Bounds F) : IntegralOriginalCriticalBounds.Inputs (source F) where
  coefficientHeight := H.coefficientHeight
  retainedHeight c := H.retainedHeight c + (F.ambient c + 1) * H.scaleHeight c
  denominatorHeight c := (F.ambient c + 1) * H.scaleHeight c
  leadingHeight := H.leadingHeight
  coefficient c e r t := by
    let := (source F).ring c
    change (Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis
      ((((F.data c).low.map (Int.castRingHom (F.scalarPrefix c).carrier)).coeff e)) r t).natAbs ≤ _
    rw [MvPolynomial.coeff_map]
    exact integer_entry_height _ _ _ (H.coefficient c e) r t
  retained c i r t := by
    let := (source F).ring c
    change (Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis
      (CoordinateFrozenCriticalElimination.numerators (F.data c).scales (F.data c).heights i.val) r t).natAbs ≤ _
    have HI : i.val < F.ambient c + 1 := i.isLt
    rw [CoordinateFrozenCriticalElimination.numerators, dite_eq_left HI]
    have HE := CommonIntegerDenominator.numerator_height (F.scalarPrefix c).basis.finBasis Finset.univ
      (F.data c).scales (F.data c).heights (H.retainedHeight c) (H.scaleHeight c)
      (fun j _ => H.scale c j) (⟨i.val, HI⟩ : Fin (F.ambient c + 1)) (H.retained c ⟨i.val, HI⟩) r t
    simpa only [Finset.card_univ, Fintype.card_fin] using HE
  denominator c := by
    have HE := CommonIntegerDenominator.denominator_height Finset.univ (F.data c).scales (H.scaleHeight c)
      (fun j _ => H.scale c j)
    simpa only [source, IntegralCanonicalCriticalBits.source, IntegralCanonicalCriticalBits.normalized,
      euler, original, CoordinateFrozenCriticalElimination.denominator, Finset.card_univ, Fintype.card_fin] using HE
  leading := H.leading

noncomputable def budget (F : Family) (H : Bounds F) : List Bool → ℕ :=
  IntegralOriginalCriticalBounds.budget (source F) (inputs F H)

theorem coefficient_height (F : Family) (H : Bounds F) (c : List Bool) (k : ℕ)
    (r t : Fin (count (F.birth c) (F.width c))) :
    (Algebra.leftMulMatrix (F.scalarPrefix c).basis.finBasis ((show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c).coeff k) r t).natAbs ≤
      2 ^ budget F H c :=
  IntegralOriginalCriticalBounds.coefficient_height (source F) (inputs F H) c k r t

theorem budget_binary (F : Family) (H : Bounds F) (a : IntegralEulerBits.Access (euler F))
    (hi : BinaryFn (fun c => (F.coordinate c).val)) (hk : BinaryFn F.coefficientIndex)
    (hC : BinaryFn H.coefficientHeight) (hV : BinaryFn H.retainedHeight)
    (hG : BinaryFn H.scaleHeight) (hP : BinaryFn H.leadingHeight) : BinaryFn (budget F H) :=
  IntegralOriginalCriticalBounds.budget_binary (source F) (inputs F H)
    (IntegralCanonicalCriticalBits.access (euler F) a F.coordinate F.coefficientIndex hi hk)
    hC (hV.add ((BinaryFn.ofUnary a.arity).mul hG)) ((BinaryFn.ofUnary a.arity).mul hG) hP

noncomputable def heightFactor (F : Family) (c : List Bool) : ℕ :=
  IntegralOriginalCriticalFactorBounds.factor (source F) c * (F.ambient c + 2)

theorem budget_scaled (F : Family) (H : Bounds F) (c : List Bool) (T : ℕ) (hT : 1 ≤ T)
    (hC : H.coefficientHeight c ≤ T) (hV : H.retainedHeight c ≤ T)
    (hG : H.scaleHeight c ≤ T) (hP : H.leadingHeight c ≤ T) : budget F H c ≤ heightFactor F c * T := by
  have HT : T ≤ (F.ambient c + 2) * T := by nlinarith
  have HV : H.retainedHeight c + (F.ambient c + 1) * H.scaleHeight c ≤ (F.ambient c + 2) * T := by
    have HG := Nat.mul_le_mul_left (F.ambient c + 1) hG
    nlinarith
  have HQ : (F.ambient c + 1) * H.scaleHeight c ≤ (F.ambient c + 2) * T := by
    exact (Nat.le_add_left _ _).trans HV
  exact (IntegralOriginalCriticalFactorBounds.budget_scaled (source F) (inputs F H) c _ (hT.trans HT)
    (hC.trans HT) HV HQ (hP.trans HT)).trans_eq (by unfold heightFactor; ring)

end LeanCanny.Algebra.IntegralHistoryCriticalBits
