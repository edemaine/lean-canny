/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackSource
public import LeanCanny.Algebra.IntegralMixedFramedCompanionEntry
/-! # Arbitrary-modulus packets retain their literal creating matrix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
attribute [local irreducible] PaddedIntegralGeneratorSource.Source.matrix
  IntegralMixedFramedCompanionBits.entry

theorem entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra))
    (q : List Bool) (r c : ℕ) :
    IntegralMixedFramedCompanionBits.entry (parameters P project extra) (plan P D project extra) Hnew q r c=
      IntegralMixedFramedCompanionBits.entry P D H (key project q) r c := by
  unfold IntegralMixedFramedCompanionBits.entry
  apply IntegralMixedFramedCompanionBits.cyclicEntry_congr _ _ _ _ _ (source_matrix P D H project extra Hnew q)
  rw [IntegralMixedFramedCompanionBits.source_arity,IntegralMixedFramedCompanionBits.source_arity,
    IntegralMixedFramedCompanionBits.source_width,IntegralMixedFramedCompanionBits.source_width,
    key_root,key_prefix]
  rfl

def packet (project : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pair (key project (PaddedIntegralGeneratorSource.base q)) (PaddedIntegralGeneratorSource.modulus q))
    (pair (PaddedIntegralGeneratorSource.row q) (PaddedIntegralGeneratorSource.col q))

theorem packet_FP (project : List Bool → List Bool) (hp : project∈FP) : packet project∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp PaddedIntegralGeneratorSource.base_FP (key_FP project hp))
    PaddedIntegralGeneratorSource.modulus_FP)
      (mem_FP_pair PaddedIntegralGeneratorSource.row_FP PaddedIntegralGeneratorSource.col_FP)

theorem value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (parameters P project extra) (plan P D project extra)) (q : List Bool) :
    PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source (parameters P project extra)
      (plan P D project extra) Hnew) q=
    PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) (packet project q) := by
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (packet project q)=
      IntegralMixedFramedCompanionQueryBits.callerModulus q := by
    simp only [IntegralMixedFramedCompanionQueryBits.callerModulus,packet,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  rw [IntegralMixedFramedCompanionBits.source_value_entry,IntegralMixedFramedCompanionBits.source_value_entry,HM]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
  simp only [packet,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
    pairFst_pair,pairSnd_pair]
  exact entry P D H project extra Hnew _ _ _

end LeanCanny.Algebra.IntegralMixedFramedRootPullback
