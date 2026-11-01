/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAffineMatrix
public import LeanCanny.Algebra.IntegralMixedHeightCofactor
public import LeanCanny.Algebra.IntegralMixedVirtualHeight
/-! # Explicit integer entries of physical and swept affine heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightMatrix
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedAffineCoefficients
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def affineEntry (x : State P S B m ι) (e : AffineExpr)
    (u v : Fin (FixedWidthPolynomial.count m B)) : ℤ :=
  (commonDenominator x * constantCoefficient e) * (if u = v then 1 else 0) +
    ∑ i : Fin m, referenceCoefficient e i.val *
      Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (cleared x i) u v

theorem entry (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (i : Fin (n + 1)) (u v : Fin (FixedWidthPolynomial.count m B)) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      (CoordinateFrozenCriticalElimination.numerators (data x hm r).scales (data x hm r).heights i.val) u v =
      IntegralMixedHeightCofactor.value x r i * affineEntry x (r.heights i) u v := by
  let _ := x.sampler.scalarPrefix.ring
  rw [IntegralMixedHeightCofactor.height, ← zsmul_eq_mul, map_zsmul, Matrix.smul_apply,
    zsmul_eq_mul, IntegralMixedAffineMatrix.entry]
  rfl

theorem virtual_constant (x : State P S B m ι) (hm : m ≤ S) (r : IntegralMixedCriticalSweep.Rule n)
    (i : Fin (n + 1)) (u v : Fin (FixedWidthPolynomial.count m B)) :
    Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      (IntegralMixedVirtualHeight.constant x hm r i.val) u v =
      IntegralMixedHeightCofactor.value x r.critical i * affineEntry x (r.critical.heights i) u v :=
  entry x hm r.critical i u v

theorem virtual_slope (x : State P S B m ι) (hm : m ≤ S) (r : IntegralMixedCriticalSweep.Rule n)
    (i : Fin (n + 1)) :
    IntegralMixedVirtualHeight.slope x hm r i.val =
      if i = r.height then r.slope * IntegralMixedHeightCofactor.value x r.critical i else 0 := by
  rw [IntegralMixedVirtualHeight.slope, dite_eq_left i.isLt, IntegralMixedHeightCofactor.erased_scales]

end LeanCanny.Algebra.IntegralMixedHeightMatrix
