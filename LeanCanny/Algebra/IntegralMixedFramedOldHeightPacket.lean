/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryValue
public import LeanCanny.Algebra.IntegralMixedFramedCompanionUniformSpace
/-! # Honest arbitrary-modulus transport of old common-cleared source packets -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (q : List Bool) := pair (IntegralMixedFramedModulusPacket.packet (source q)) (pairSnd q)
theorem packet_FP : packet∈FP :=
  mem_FP_pair (mem_FP_comp (f:=source) (g:=IntegralMixedFramedModulusPacket.packet) pairFst_mem_FP IntegralMixedFramedModulusPacket.packet_FP) pairSnd_mem_FP

theorem packet_root (q : List Bool) : root (packet q)=pair (root q) (PaddedIntegralGeneratorSource.modulus (source q)) := by
  simpa only [root,key,source,packet,pairFst_pair,IntegralMixedFramedCompanionQueryBits.root] using
    IntegralMixedFramedModulusPacket.packet_root (pairFst q)
theorem packet_birth (P : Parameters) (q : List Bool) : sourceBirth (lifted P) (packet q)=sourceBirth P q := by
  simpa only [sourceBirth,key,source,packet,pairFst_pair,IntegralMixedFramedCompanionQueryBits.sourceBirth] using
    IntegralMixedFramedModulusPacket.packet_birth P (pairFst q)
theorem packet_modulus (q : List Bool) : callerModulus (packet q)=callerModulus q := by
  simpa only [callerModulus,source,packet,pairFst_pair] using
    IntegralMixedFramedModulusPacket.packet_modulus (pairFst q)
theorem packet_active (P : Parameters) (q : List Bool) : Active (lifted P) (packet q) ↔ Active P q := by
  rw [Active,packet_birth,packet_root]
  simp only [lifted,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,Active]

theorem packet_rank (P : Parameters) (q : List Bool) : sourceRank (lifted P) (packet q)=sourceRank P q := by
  rw [sourceRank,packet_birth,packet_root]
  simp only [lifted,IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair,sourceRank]

theorem packet_index (P : Parameters) (q : List Bool) : retainedIndex (lifted P) (packet q)=retainedIndex P q := by
  unfold retainedIndex
  rw [packet_birth]
  simp only [packet,pairSnd_pair]

theorem packet_row (P : Parameters) (q : List Bool) : rowIndex (lifted P) (packet q)=rowIndex P q := by
  rw [rowIndex,packet_rank]
  simp only [source,packet,pairFst_pair,IntegralMixedFramedModulusPacket.packet,PaddedIntegralGeneratorSource.row,pairSnd_pair]
  rfl

theorem packet_col (P : Parameters) (q : List Bool) : colIndex (lifted P) (packet q)=colIndex P q := by
  rw [colIndex,packet_rank]
  simp only [source,packet,pairFst_pair,IntegralMixedFramedModulusPacket.packet,PaddedIntegralGeneratorSource.col,pairSnd_pair]
  rfl

theorem value_planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) :
    value (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) q=value P D H q := by
  unfold value
  rw [IntegralMixedFramedOldHeightBankBits.sourceEntry_planned]
  rfl

theorem value_pullback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    value (lifted P) (liftedPlan P D)
      (IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra) (packet q)=value P D H q := by
  by_cases hb : Active P q
  · rw [value,ite_eq_left ((packet_active P q).mpr hb),value,ite_eq_left hb,
      packet_modulus,packet_index,packet_row,packet_col]
    apply congrArg (fun z : ℤ => residueBits (z : ZMod (callerModulus q)))
    rw [IntegralMixedFramedOldHeightBankBits.sourceEntry_root,
      IntegralMixedFramedOldHeightBankBits.rootEntry_pullback,
      IntegralMixedFramedOldHeightBankBits.sourceEntry_root]
    change IntegralMixedFramedOldHeightBankBits.rootEntry P D H (pairFst (root (packet q)))
      (sourceBirth (lifted P) (packet q)) _ _ _=IntegralMixedFramedOldHeightBankBits.rootEntry P D H (root q) (sourceBirth P q) _ _ _
    rw [packet_root,packet_birth,pairFst_pair]
  · rw [value,ite_eq_right (fun h => hb ((packet_active P q).mp h)),value,ite_eq_right hb]

end LeanCanny.Algebra.IntegralMixedFramedOldHeightQueryBits
