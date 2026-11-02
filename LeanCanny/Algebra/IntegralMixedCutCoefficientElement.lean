/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutCoefficientReadback
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeSource
/-! # Indexed finite probes read the actual coefficient in the original algebra -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutCoefficientQueryBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

private theorem coefficient_key (F : IntegralMixedCutSource.Family) (u v : List Bool) (he : u=v) (e k : ℕ) :
    HEq ((IntegralMixedRelativeCuts.factor (F.state u) (F.birth_bound u) (F.rule u)
      (IntegralMixedRelativeCuts.atChoice (F.rule u) (F.kind u) k)).coeff e)
      ((IntegralMixedRelativeCuts.factor (F.state v) (F.birth_bound v) (F.rule v)
      (IntegralMixedRelativeCuts.atChoice (F.rule v) (F.kind v) k)).coeff e) := by
  cases he
  rfl

theorem element_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : List Bool) (e k : ℕ) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (he : e≤2^P.width (RankedHistoryTask.root c)) (hk : k≤2^P.width (RankedHistoryTask.root c)) :
    HEq ((IntegralMixedFramedChoiceProbeSourceBits.source P D H).element
      (query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)))))
      ((IntegralMixedRelativeCuts.factor ((family P D H).state (IntegralMixedVirtualTaskBits.saved P c))
        ((family P D H).birth_bound _) ((family P D H).rule _) (IntegralMixedRelativeCuts.atChoice
          ((family P D H).rule _) ((family P D H).kind _) k)).coeff e) := by
  have hqa : IntegralMixedFramedFullCutProbeBits.Active P
      (query P (pair c (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)))) :=
    (query_active P _).mpr (by simpa only [pairFst_pair] using ha)
  simp only [IntegralMixedFramedChoiceProbeSourceBits.source,ite_eq_left hqa]
  simp only [IntegralMixedRawKindChoiceBits.requested]
  rw [coefficient_packet P c e k he,choice_packet P c e k hk]
  exact coefficient_key (family P D H) _ _ ((query_saved P _).trans (congrArg (IntegralMixedVirtualTaskBits.saved P) (pairFst_pair _ _))) e k

end LeanCanny.Algebra.IntegralMixedCutCoefficientQueryBits
