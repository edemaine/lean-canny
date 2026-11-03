/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalRowOrigin
public import LeanCanny.Algebra.IntegralMixedFramedCompanionQueryReadback
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalHeightSource
/-! # Original-header source tasks for full physical row creators

The datum is a pair of a full-row selector packet and a caller modulus code.
Only the original saved root, creator birth and command header are read.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalBirthQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedPhysicalRowSelector
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedCompanionQueryBits.query
  IntegralMixedCommandHeaderBits.lookup IntegralMixedFramedHistoryFamilyBits.instruction

def packet (P : Parameters) (T : Tables) (q : List Bool) :=
  pair (pair (previousKey P T (pairFst q)) (pairSnd q)) (pair [] [])

attribute [local irreducible] packet

theorem packet_FP (P : Parameters) (a : Access P) (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T) :
    packet P T∈FP := by
  exact mem_FP_of_eq (mem_FP_pair (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP (previousKey_FP P a T ht)) pairSnd_mem_FP)
    (constFn_mem_FP (pair [] []))) (fun _=>by unfold packet; rfl)

noncomputable def base (P : Parameters) (D : Plan P) (T : Tables) :=
  IntegralMixedFramedCompanionQueryBits.query P D∘packet P T

attribute [local irreducible] base

theorem base_FP (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D J T) :
    base P D T∈FP :=
  mem_FP_of_eq (mem_FP_comp (packet_FP P a T ht) (IntegralMixedFramedCompanionQueryBits.query_FP P a D J T ht hr))
    (fun _=>by unfold base; rfl)

theorem base_root (P : Parameters) (D : Plan P) (T : Tables) (q : List Bool) :
    RankedHistoryTask.root (base P D T q)=pairFst (pairFst (pairFst q)) := by
  rw [base,Function.comp_apply,IntegralMixedFramedCompanionQueryBits.query_root]
  simp only [IntegralMixedFramedCompanionQueryBits.root,PaddedIntegralGeneratorSource.base,packet,
    pairFst_pair,previousKey]

theorem base_birth (P : Parameters) (D : Plan P) (T : Tables) (q : List Bool)
    (hb : rowBirth P T (pairFst q)≤P.cap (pairFst (pairFst (pairFst q)))+1) :
    birth P (base P D T q)=rowBirth P T (pairFst q) := by
  rw [base,Function.comp_apply,IntegralMixedFramedCompanionQueryBits.query_birth]
  simp only [IntegralMixedFramedCompanionQueryBits.sourceBirth,PaddedIntegralGeneratorSource.base,packet,
    pairFst_pair,previousKey]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ hb

theorem base_modulus (P : Parameters) (D : Plan P) (T : Tables) (q : List Bool)
    (hm : Nat.fromBitsLE (pairSnd q)+1≤numericCap P (pairFst (pairFst (pairFst q)))) :
    modulus P (base P D T q)=Nat.fromBitsLE (pairSnd q)+1 := by
  have HR : IntegralMixedFramedCompanionQueryBits.root (packet P T q)=pairFst (pairFst (pairFst q)) := by
    simp only [IntegralMixedFramedCompanionQueryBits.root,PaddedIntegralGeneratorSource.base,packet,
      pairFst_pair,previousKey]
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus (packet P T q)=Nat.fromBitsLE (pairSnd q)+1 := by
    simp only [IntegralMixedFramedCompanionQueryBits.callerModulus,PaddedIntegralGeneratorSource.modulus,packet,pairFst_pair,pairSnd_pair]
  rw [base,Function.comp_apply,IntegralMixedFramedCompanionQueryBits.query_modulus P D _ (by rw [HR,HM];exact hm),HM]

theorem base_actual_context (P : Parameters) (D : Plan P) (T : Tables) (q : List Bool) :
    get P .slot15 (base P D T q)=
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (IntegralMixedVirtualTaskBits.saved P (base P D T q))).command.context := by
  unfold base
  exact IntegralMixedFramedCompanionQueryBits.query_actual_context P D (packet P T q)

theorem previous_prefix (P : Parameters) (T : Tables) (key : List Bool) (r : ℕ)
    (hb : rowBirth P T (pair key (BinaryNatCode.encode r))≤P.cap (pairFst key)+1) :
    IntegralMixedFramedHistoryFamilyBits.prefixLength P (previousKey P T (pair key (BinaryNatCode.encode r)))=
      rowBirth P T (pair key (BinaryNatCode.encode r)) := by
  unfold previousKey
  rw [pairFst_pair]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P _ _ _ hb

theorem base_context (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) (M : List Bool) :
    get P .slot15 (base P D T (pair (pair key (BinaryNatCode.encode r)) M))=1 := by
  have HB:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_below_cap P D J T hT key r hr hs
  have HC:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_context P T key r hr hs
  have HE : IntegralMixedHeaderTablesBits.producer P T (previousKey P T (pair key (BinaryNatCode.encode r)))=
      IntegralMixedFramedPhysicalRowDegree.header P T (pair key (BinaryNatCode.encode r)) := by
    unfold IntegralMixedHeaderTablesBits.producer IntegralMixedFramedPhysicalRowDegree.header
    have HR : pairFst (previousKey P T (pair key (BinaryNatCode.encode r)))=pairFst key := by
      unfold previousKey
      simp only [pairFst_pair]
    rw [HR,pairFst_pair]
    exact congrArg (IntegralMixedCommandHeaderBits.lookup (T.commands (pairFst key)))
      (previous_prefix P T key r (by omega))
  have HP:=congrArg IntegralMixedCommandHeaderBits.Header.context
    (IntegralMixedFramedHeaderBits.producer_eq P D J T hT (previousKey P T (pair key (BinaryNatCode.encode r))))
  rw [HE] at HP
  have HQ : (IntegralMixedFramedHistoryFamilyBits.instruction P D
      (previousKey P T (pair key (BinaryNatCode.encode r)))).command.context=1 :=
    (HP.trans (IntegralMixedCommandHeaderBits.command_context
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (previousKey P T (pair key (BinaryNatCode.encode r)))).command)).symm.trans HC
  rw [base,Function.comp_apply,IntegralMixedFramedCompanionQueryBits.query_context]
  have HPB : PaddedIntegralGeneratorSource.base (packet P T (pair (pair key (BinaryNatCode.encode r)) M))=
      previousKey P T (pair key (BinaryNatCode.encode r)) :=by
    unfold PaddedIntegralGeneratorSource.base packet
    simp only [pairFst_pair]
  unfold IntegralMixedFramedCompanionQueryBits.context
  rw [HPB]
  exact HQ

theorem base_active (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : Tables) (hT : IntegralMixedFramedHeaderBits.Represents P D J T) (key : List Bool) (r : ℕ)
    (hr : r<fullArity P T (pair key (BinaryNatCode.encode r)))
    (hs : ¬IsScalar P T (pair key (BinaryNatCode.encode r))) (M : List Bool) :
    IntegralMixedFramedPhysicalHeightBits.Active P (base P D T (pair (pair key (BinaryNatCode.encode r)) M)) := by
  have HB:=IntegralMixedFramedPhysicalRowOrigin.nonScalar_below_cap P D J T hT key r hr hs
  refine ⟨?_,base_context P D J T hT key r hr hs M⟩
  unfold IntegralMixedVirtualCaps.valid
  rw [base_birth P D T _ (by simp only [pairFst_pair];omega),base_root]
  simpa only [pairFst_pair] using HB

end LeanCanny.Algebra.IntegralMixedFramedPhysicalBirthQueryBits
