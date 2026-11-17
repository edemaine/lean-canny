/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SparseIntegerRootLabels
public import LeanCanny.CountingHierarchy.NativeBinaryBounds

/-! # Polynomial-time binary computation of root-label resource bounds -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem derivativeTestMassExponent_polyTime {D b : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => derivativeTestMassExponent (D w) (b w)) enc encNat := by
  exact ComputableInPolyTime.binary_add' hb
    (ComputableInPolyTime.binary_mul' (binarySize_polyTime hD) hD)

@[fun_prop] theorem algebraicTestPrecision_polyTime {D E bp bg : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hE : ComputableInPolyTime E enc encNat)
    (hp : ComputableInPolyTime bp enc encNat) (hg : ComputableInPolyTime bg enc encNat) :
    ComputableInPolyTime (fun w => algebraicTestPrecision (D w) (E w) (bp w) (bg w))
      enc encNat := by
  have hDE := ComputableInPolyTime.binary_add' hD hE
  have hmass := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (binarySize_polyTime hDE) hDE)
    (ComputableInPolyTime.binary_mul' hDE
      (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_add' hp hg) (.const 1)))
  have hlower := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' hmass
      (binarySize_polyTime (ComputableInPolyTime.binary_add' hD (.const 1))))
    (.const 1)
  exact ComputableInPolyTime.binary_add' hlower
    (ComputableInPolyTime.binary_add' hg
      (ComputableInPolyTime.binary_mul' hE (ComputableInPolyTime.binary_add' hp (.const 1))))

@[fun_prop] theorem rootLabelDegreeBound_polyTime {m B s D : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat) (hD : ComputableInPolyTime D enc encNat) :
    ComputableInPolyTime (fun w => rootLabelDegreeBound (m w) (B w) (s w) (D w))
      enc encNat := by
  have hfactor := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_mul' (.const 2) hs)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' (.const 2) hB) (.const 1))
  exact ComputableInPolyTime.binary_mul' (.const 2)
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_add' hm (.const 1))
      (ComputableInPolyTime.binary_mul' hfactor hD))

@[fun_prop] theorem rootLabelMassExponent_polyTime {m B s b : α → ℕ}
    (hm : ComputableInPolyTime m enc encNat) (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => rootLabelMassExponent (m w) (B w) (s w) (b w))
      enc encNat := by
  have hfactor := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_mul' (.const 2) hs)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' (.const 2) hB) (.const 1))
  have htest := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_mul' hfactor (ComputableInPolyTime.binary_add' hB (.const 1)))
      (ComputableInPolyTime.binary_mul' hfactor hb)) (.const 1)
  exact ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' (binarySize_polyTime hm)
      (ComputableInPolyTime.binary_mul' (.const 2)
        (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_add' hm (.const 1)) htest)))
    (.const 5)

@[fun_prop] theorem sparseRootLabelDegreeBound_polyTime {D N b : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hN : ComputableInPolyTime N enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => sparseRootLabelDegreeBound (D w) (N w) (b w))
      enc encNat := by
  exact rootLabelDegreeBound_polyTime (ComputableInPolyTime.binary_add' hN (.const 1))
    (algebraicTestPrecision_polyTime hD hD hb (derivativeTestMassExponent_polyTime hD hb))
    (ComputableInPolyTime.binary_mul' (.const 16) (ComputableInPolyTime.binary_add' hN (.const 1))) hD

@[fun_prop] theorem sparseRootLabelMassExponent_polyTime {D N b : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hN : ComputableInPolyTime N enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => sparseRootLabelMassExponent (D w) (N w) (b w))
      enc encNat := by
  exact rootLabelMassExponent_polyTime (ComputableInPolyTime.binary_add' hN (.const 1))
    (algebraicTestPrecision_polyTime hD hD hb (derivativeTestMassExponent_polyTime hD hb))
    (ComputableInPolyTime.binary_mul' (.const 16) (ComputableInPolyTime.binary_add' hN (.const 1)))
    (derivativeTestMassExponent_polyTime hD hb)

end LeanCanny.CountingHierarchy
