/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackValue
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQuerySpace
/-! # Preserve arbitrary caller moduli by augmenting the original root

The additional root field stores the caller's modulus word. The projection
retains the complete original root, while creating keys retain their original
birth/context tail. Source matrices and residues are unchanged.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedModulusPacket
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedFramedCompanionQueryBits (root sourceBirth callerModulus)
open scoped Classical

def extra (root : List Bool) : ℕ := Nat.fromBitsLE (pairSnd root)+1
theorem extra_binary : BinaryFn extra := (BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)

def originalKey (q : List Bool) : List Bool :=
  pair (pair (root q) (PaddedIntegralGeneratorSource.modulus q)) (pairSnd (PaddedIntegralGeneratorSource.base q))

theorem originalKey_FP : originalKey∈FP :=
  mem_FP_pair (mem_FP_pair IntegralMixedFramedCompanionQueryBits.root_FP PaddedIntegralGeneratorSource.modulus_FP)
    (mem_FP_comp PaddedIntegralGeneratorSource.base_FP pairSnd_mem_FP)

def packet (q : List Bool) : List Bool :=
  pair (pair (originalKey q) (PaddedIntegralGeneratorSource.modulus q))
    (pair (PaddedIntegralGeneratorSource.row q) (PaddedIntegralGeneratorSource.col q))

theorem packet_FP : packet∈FP :=
  mem_FP_pair (mem_FP_pair originalKey_FP PaddedIntegralGeneratorSource.modulus_FP)
    (mem_FP_pair PaddedIntegralGeneratorSource.row_FP PaddedIntegralGeneratorSource.col_FP)

theorem packet_root (q : List Bool) : root (packet q)=pair (root q) (PaddedIntegralGeneratorSource.modulus q) := by
  simp only [root,PaddedIntegralGeneratorSource.base,packet,originalKey,pairFst_pair]

theorem packet_birth (P : Parameters) (q : List Bool) :
    sourceBirth (IntegralMixedFramedRootPullback.parameters P pairFst extra) (packet q)=sourceBirth P q := by
  simp only [sourceBirth,prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,
    IntegralMixedFramedRootPullback.parameters,Function.comp_apply,packet,originalKey,
    PaddedIntegralGeneratorSource.base,pairFst_pair,pairSnd_pair,root]

theorem packet_modulus (q : List Bool) : callerModulus (packet q)=callerModulus q := by
  simp only [callerModulus,PaddedIntegralGeneratorSource.modulus,packet,pairFst_pair,pairSnd_pair]

theorem packet_modulus_le (P : Parameters) (q : List Bool) :
    callerModulus (packet q)≤numericCap (IntegralMixedFramedRootPullback.parameters P pairFst extra) (root (packet q)) := by
  rw [packet_root,packet_modulus]
  simpa only [extra,callerModulus,pairSnd_pair] using
    IntegralMixedFramedRootPullback.modulus_budget P pairFst extra
      (pair (root q) (PaddedIntegralGeneratorSource.modulus q))

theorem packet_representable (P : Parameters) (q : List Bool) (hb : sourceBirth P q<P.cap (root q)) :
    IntegralMixedFramedCompanionQueryBits.Representable
      (IntegralMixedFramedRootPullback.parameters P pairFst extra) (packet q) := by
  refine ⟨?_,packet_modulus_le P q⟩
  rw [packet_birth,packet_root]
  simpa only [IntegralMixedFramedRootPullback.parameters,Function.comp_apply,pairFst_pair] using hb

theorem projected_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H)
      (IntegralMixedFramedRootPullback.packet pairFst (packet q))=
    PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HM : callerModulus (IntegralMixedFramedRootPullback.packet pairFst (packet q))=callerModulus q := by
    simp only [callerModulus,IntegralMixedFramedRootPullback.packet,packet,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  rw [IntegralMixedFramedCompanionBits.source_value_entry,IntegralMixedFramedCompanionBits.source_value_entry,HM]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (callerModulus q)))
  simp only [IntegralMixedFramedRootPullback.packet,packet,originalKey,IntegralMixedFramedRootPullback.key,
    PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
    pairFst_pair,pairSnd_pair,root]
  apply IntegralMixedFramedCompanionBits.entry_congr
  · exact pairFst_pair _ _
  · simp only [prefixLength,IntegralMixedFullHistoryFamilyBits.prefixLength,pairFst_pair,pairSnd_pair]

theorem source_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedRootPullback.parameters P pairFst extra)
      (IntegralMixedFramedRootPullback.plan P D pairFst extra)) (q : List Bool) :
    PaddedIntegralGeneratorSource.value
      (IntegralMixedFramedCompanionBits.source (IntegralMixedFramedRootPullback.parameters P pairFst extra)
        (IntegralMixedFramedRootPullback.plan P D pairFst extra) Hnew) (packet q)=
    PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q :=
  (IntegralMixedFramedRootPullback.value P D H pairFst extra Hnew (packet q)).trans (projected_value P D H q)

end LeanCanny.Algebra.IntegralMixedFramedModulusPacket
