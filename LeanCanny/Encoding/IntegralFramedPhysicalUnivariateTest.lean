/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareAccess
public import LeanCanny.Encoding.SquareSampleCompleteUnivariateTest
public import LeanCanny.Geometry.IntegralMixedFramedBankUnivariateSign
/-! # Untruncated original integer tests at a full physical sample

The datum selects a retained bank index. Its actual scalar injection into
all physical variables selects the raw coordinate; the full context and
vertex never change. Even common-denominator clearing preserves the sign
of the original polynomial, including its value at padding zero.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalUnivariateTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedPhysicalIndex (enumerate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c))
local notation "S"=>IntegralFramedPhysicalSquare.input P D H L F C hs key hpos

def saved (key : List Bool→List Bool) (z : List Bool) :=key (pairFst z)
noncomputable def selected (coordinate : (c d : List Bool)→Fin ((family P D H).birth (key c))) (z : List Bool) :=
  (coordinate (pairFst z) (pairSnd z)).val
noncomputable def column (coordinate : (c d : List Bool)→Fin ((family P D H).birth (key c)))
    (c d : List Bool) : Fin (IntegralFramedPhysicalSquare.count P D (key c)) :=
  enumerate (commands P D (key c)) (((family P D H).state (key c)).sampler.scalar (coordinate c d))
noncomputable def source (coordinate : (c d : List Bool)→Fin ((family P D H).birth (key c)))
    (Q : IntegerPolynomialRootQueriesBits.Source) :=
  IntegralMixedFramedBankUnivariateSource.source P D H L F C hs (saved key) (selected P D H key coordinate) Q
noncomputable def value (coordinate : (c d : List Bool)→Fin ((family P D H).birth (key c)))
    (Q : IntegerPolynomialRootQueriesBits.Source) :=
  SquareSampleCompleteUnivariateTest.value S (source P D H L F C hs key coordinate Q) (column P D H key coordinate)

variable (coordinate : (c d : List Bool)→Fin ((family P D H).birth (key c)))
  (Q : IntegerPolynomialRootQueriesBits.Source)

theorem packet (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    value P D H L F C hs key hpos coordinate Q (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ)
        (IntegralFramedPhysicalSquare.point P D H L F C hs key hpos c w hv (coordinate c d)))) := by
  rw [value,SquareSampleCompleteUnivariateTest.packet _ _ _ c w d hv]
  have HN : (IntegralMixedFramedBankScalars.scalars P D H L F C hs
      (saved key) (selected P D H key coordinate)).denominator (pair c d)≠0 := by
    simpa only [IntegralMixedFramedBankScalars.scalars,saved,pairFst_pair] using
      LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero P D H (key c)
  rw [source,IntegralMixedFramedBankUnivariateSource.source,IntegerPolynomialRationalPointSource.sign _ _ _ _ _ HN]
  apply congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ) v)))
  dsimp only [IntegralMixedFramedBankScalars.scalars,IntegralMixedFramedBankUnivariateSource.power,
    saved,selected]
  rw [pairFst_pair,pairSnd_pair]
  change ((IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).cofactor (coordinate c d).val:ℝ)*
      (IntegralFramedPhysicalSquare.joint P D H L F C hs key hpos c w hv (column P D H key coordinate c d))^
        UniformIntegralPowerSchedule.weights ((family P D H).cap (key c)) (2^(family P D H).width (key c))
          ((family P D H).birth (key c)) (coordinate c d)/
      ((IntegralMixedFramedBankSnapshotBits.atKey P D H (key c)).common:ℝ)=_
  unfold IntegralFramedPhysicalSquare.point LeanCanny.Geometry.IntegralMixedFullBankPoint.indexedPoint
    LeanCanny.Geometry.IntegralMixedFullBankPoint.point LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
  apply (div_eq_div_iff (Int.cast_ne_zero.mpr (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.common_ne_zero P D H (key c)))
    (Int.cast_ne_zero.mpr (((family P D H).state (key c)).denominator_ne_zero (coordinate c d)))).mpr
  rw [LeanCanny.Geometry.IntegralMixedFramedBankTermSign.snapshot_split _ (coordinate c d),Int.cast_mul]
  dsimp only [column,Function.comp_apply,IntegralMixedFramedBankSnapshotBits.atKey]
  have HC (a b c : ℝ) : a*b*c=b*(c*a) :=by ring
  exact HC _ _ _

end LeanCanny.Encoding.IntegralFramedPhysicalUnivariateTest
