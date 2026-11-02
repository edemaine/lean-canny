/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankTermTest
public import LeanCanny.Geometry.IntegralMixedFramedBankTermObservation
/-! # Native term-sign replies use one bank-only observation of the joint root -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankTermTest
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

noncomputable def observedPoint (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : ℕ→ℝ) (i : ℕ) :=
  if i<(atKey P D H key).count then
    (IntegralMixedFramedBankObservation.ofState
      (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state P D H key)).point z
        ((atKey P D H key).count-1-i) else 0

theorem observedPoint_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : Fin (atKey P D H key).count→ℝ) :
    observedPoint P D H key (IntegralMixedFramedBankObservation.extend z)=
      LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point P D H key z := by
  funext i
  by_cases hi : i<(atKey P D H key).count
  · unfold observedPoint
    rw [ite_eq_left hi]
    have HZ : (fun j : Fin (atKey P D H key).count=>IntegralMixedFramedBankObservation.extend z j.val)=z := by
      funext j
      exact dite_eq_left j.isLt
    have HE:=LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point_observation P D H key
      (IntegralMixedFramedBankObservation.extend z) i hi
    rw [HZ] at HE
    exact HE.symm
  · unfold observedPoint LeanCanny.Geometry.IntegralMixedFramedBankTermSign.point
    rw [ite_eq_right hi,dite_eq_right hi]

theorem packet_observation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (s : IntegralMixedFramedNativeBits.Syntax P D H)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D s.nodes s.factor s.seed) (key : List Bool→List Bool)
    (hpos : ∀ c,0<(atKey P D H (key c)).count) (word : List Bool→List Bool) (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input P D H s hs key hpos) c w) :
    value P D H s hs key hpos word (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (key c)).eval
        (observedPoint P D H (key c) (IntegralMixedFramedBankObservation.extend
          (SquareSampleCompleteVertices.candidate (input P D H s hs key hpos) c w hv).val)))) := by
  have HE := observedPoint_eq P D H (key c)
    (SquareSampleCompleteVertices.candidate (input P D H s hs key hpos) c w hv).val
  exact (packet P D H s hs key hpos word c w d hv).trans
    (congrArg (fun env : ℕ→ℝ=>InfinitesimalSign.encode
      (SignType.sign (((IntegralMixedFramedBankTermBits.source word).syntax (key c)).eval env))) HE).symm

end LeanCanny.Encoding.IntegralFramedBankTermTest
