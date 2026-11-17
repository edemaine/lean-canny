/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PrescribedRootLabelBounds
public import LeanCanny.CountingHierarchy.NativeRootLabelBounds

/-! # Polynomial-time binary budgets for prescribed-root labels -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {D b : α → ℕ}

@[fun_prop] theorem fingerprintWeightBudget_polyTime (hD : ComputableInPolyTime D enc encNat) :
    ComputableInPolyTime (fun w => fingerprintWeightBudget (D w)) enc encNat :=
  ComputableInPolyTime.binary_mul' hD (ComputableInPolyTime.binary_mul' (.const 2)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_pow' hD (.const 3)) (.const 2)))

@[fun_prop] theorem prescribedRootLabelDegreeBound_polyTime
    (hD : ComputableInPolyTime D enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => prescribedRootLabelDegreeBound (D w) (b w)) enc encNat := by
  have hB := algebraicTestPrecision_polyTime hD hD hb (derivativeTestMassExponent_polyTime hD hb)
  have hs := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 16)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.const 1) (fingerprintWeightBudget_polyTime hD))
  have h := rootLabelDegreeBound_polyTime (ComputableInPolyTime.binary_add' hD (.const 1)) hB hs hD
  simpa only [prescribedRootLabelDegreeBound, fingerprintLabelDegreeBound, rootLabelDegreeBound,
    Nat.add_assoc] using h

@[fun_prop] theorem prescribedRootLabelMassExponent_polyTime
    (hD : ComputableInPolyTime D enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => prescribedRootLabelMassExponent (D w) (b w)) enc encNat := by
  have htest := derivativeTestMassExponent_polyTime hD hb
  have hB := algebraicTestPrecision_polyTime hD hD hb htest
  have hW := fingerprintWeightBudget_polyTime hD
  have hs := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 16)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.const 1) hW)
  have hf := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hs)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2) hB)
      (ComputableInPolyTime.const 1))
  have hH := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_mul' hf (ComputableInPolyTime.binary_add' hB (.const 1)))
      (ComputableInPolyTime.binary_mul' hf htest)) (ComputableInPolyTime.const 1)
  exact ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.binary_add'
        (ComputableInPolyTime.binary_add' (binarySize_polyTime hW)
          (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_add' hD (.const 2)) hH))
        (ComputableInPolyTime.const 1))) (ComputableInPolyTime.const 5)

end LeanCanny.CountingHierarchy
