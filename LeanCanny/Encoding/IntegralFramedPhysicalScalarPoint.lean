/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalScalarRoots
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
/-! # Scalar-prefix bank points are the same full physical bank point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
 (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
 (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
 (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w)

theorem scalarTuple_point (i : Fin ((family P D H).birth (key c))) :
    IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key c))
      (scalarTuple P D H L F C hs key hpos c w hv) i=
    point P D H L F C hs key hpos c w hv i :=by
  rfl

end LeanCanny.Encoding.IntegralFramedPhysicalSquare
