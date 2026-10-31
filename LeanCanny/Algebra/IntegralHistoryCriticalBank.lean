/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryCriticalBounds

/-! # Canonical bank growth for actual critical scalar births

The sampler's retained heights and scales select actual entries of its old
canonical bank. Its constructed critical polynomial then supplies the next
bank extension. One binary factor bounds this complete birth, including
common clearing, reduction, relative characteristic coefficients, and the
canonical normalization of the selected scalar.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def bankBounds (F : Family)
    (bank : ∀ c, HeightBank (F.scalarPrefix c)) (V C P : List Bool → ℕ)
    (hbank : ∀ c, (bank c).Bounds (V c))
    (select : ∀ c, Fin (F.ambient c + 1) → Option (Fin (F.birth c)))
    (heights : ∀ c i, (F.data c).heights i = (bank c).selectedNumerator (select c i))
    (scales : ∀ c i, (F.data c).scales i = (bank c).selectedDenominator (select c i))
    (hC : ∀ c e, ((F.data c).low.coeff e).natAbs ≤ 2 ^ C c)
    (hP : ∀ c, ((F.data c).leading).natAbs ≤ 2 ^ P c) : Bounds F where
  coefficientHeight := C
  retainedHeight := V
  scaleHeight := V
  leadingHeight := P
  coefficient := hC
  retained c i r t := by
    rw [heights c i]
    exact (bank c).selected_numerator_height (V c) (hbank c) (select c i) r t
  scale c i := by
    rw [scales c i]
    exact (bank c).selected_denominator_height (V c) (hbank c) (select c i)
  leading := hP

theorem heightFactor_binary (F : Family) (a : IntegralEulerBits.Access (euler F))
    (hi : BinaryFn (fun c => (F.coordinate c).val)) (hk : BinaryFn F.coefficientIndex) : BinaryFn (heightFactor F) :=
  (IntegralOriginalCriticalFactorBounds.factor_binary (source F)
    (IntegralCanonicalCriticalBits.access (euler F) a F.coordinate F.coefficientIndex hi hk)).mul
    ((BinaryFn.ofUnary a.arity).add (BinaryFn.const 1))

theorem bank_step_bounds (F : Family) (H : Bounds F) (c : List Bool) (T R d : ℕ)
    (bank : HeightBank (F.scalarPrefix c)) (hbank : bank.Bounds T) (hT : 1 ≤ T)
    (hR : count (F.birth c) (F.width c) ≤ R)
    (hC : H.coefficientHeight c ≤ T) (hV : H.retainedHeight c ≤ T)
    (hG : H.scaleHeight c ≤ T) (hP : H.leadingHeight c ≤ T) :
    (bank.step (F.data c).birth_bound
      (show Polynomial (F.scalarPrefix c).carrier from (source F).annihilator c) d).Bounds
      (bankGrowth R (2 ^ F.width c) (heightFactor F c) * T) :=
  bank.step_scaled_bounds (F.data c).birth_bound _ d (budget F H c) T R (heightFactor F c) hbank hT hR
    (budget_scaled F H c T hT hC hV hG hP) (coefficient_height F H c)

end LeanCanny.Algebra.IntegralHistoryCriticalBits
