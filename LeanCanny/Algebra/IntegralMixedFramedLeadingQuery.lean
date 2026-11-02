/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedLeadingSource
/-! # Exact native producer-leading queries from original source packets -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable def query (P : Parameters) (D : Plan P) :=
  child P IntegralMixedFramedCompanionQueryBits.parent (IntegralMixedFramedCompanionQueryBits.sourceBirth P)
    .originalCoefficient (IntegralMixedFramedCompanionQueryBits.reader P D)

theorem query_FP (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T) : query P D∈FP :=
  child_FP P a _ IntegralMixedFramedCompanionQueryBits.parent_FP _
    (BinaryFn.ofUnary (IntegralMixedFramedCompanionQueryBits.sourceBirth_unary P a)) _ _
    (IntegralMixedFramedCompanionQueryBits.reader_FP P a D H T ht hr)

theorem query_root (P : Parameters) (D : Plan P) (q : List Bool) :
    RankedHistoryTask.root (query P D q)=RankedHistoryTask.root (IntegralMixedFramedCompanionQueryBits.query P D q) := by
  rw [query,child_root,IntegralMixedFramedCompanionQueryBits.query_root]
  exact pairFst_pair _ _

theorem query_get (P : Parameters) (D : Plan P) (q : List Bool) (f : Field) :
    get P f (query P D q)=get P f (IntegralMixedFramedCompanionQueryBits.query P D q) := by
  rw [query,child_get,IntegralMixedFramedCompanionQueryBits.query_get,IntegralMixedFramedCompanionQueryBits.reader_packet]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedFramedCompanionQueryBits.parent,
    RankedHistoryTask.root,pairFst_pair]

theorem query_birth (P : Parameters) (D : Plan P) (q : List Bool) :
    birth P (query P D q)=birth P (IntegralMixedFramedCompanionQueryBits.query P D q) := by
  rw [IntegralMixedFramedCompanionQueryBits.query_birth]
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (by
    simp only [IntegralMixedFramedCompanionQueryBits.sourceBirth,IntegralMixedFramedHistoryFamilyBits.prefixLength,
      IntegralMixedFullHistoryFamilyBits.prefixLength,birthCap,IntegralMixedFramedCompanionQueryBits.parent,
      RankedHistoryTask.root,pairFst_pair]
    exact min_le_right _ _)

theorem query_phase (P : Parameters) (D : Plan P) (q : List Bool) : phase (query P D q)=0 := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ (by decide)

theorem query_saved (P : Parameters) (D : Plan P) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P D q)=
      IntegralMixedVirtualTaskBits.saved P (IntegralMixedFramedCompanionQueryBits.query P D q) := by
  simp only [IntegralMixedVirtualTaskBits.saved,query_root,query_birth,query_get]

theorem query_routine (P : Parameters) (D : Plan P) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (query P D q)=6 := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [query_get]
  exact IntegralMixedFramedCompanionQueryBits.query_routine P D q

theorem query_modulus (P : Parameters) (D : Plan P) (q : List Bool)
    (hm : IntegralMixedFramedCompanionQueryBits.callerModulus q≤numericCap P (IntegralMixedFramedCompanionQueryBits.root q)) :
    modulus P (query P D q)=IntegralMixedFramedCompanionQueryBits.callerModulus q := by
  unfold modulus
  rw [query_get]
  exact IntegralMixedFramedCompanionQueryBits.query_modulus P D q hm

theorem query_valid (P : Parameters) (D : Plan P) (q : List Bool)
    (hb : IntegralMixedFramedCompanionQueryBits.sourceBirth P q<P.cap (IntegralMixedFramedCompanionQueryBits.root q)) :
    IntegralMixedVirtualCaps.valid P (query P D q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_root,query_birth]
  exact IntegralMixedFramedCompanionQueryBits.query_valid P D q hb

theorem model_query (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedNativeBits.Controls P D H) (q : List Bool)
    (hb : IntegralMixedFramedCompanionQueryBits.sourceBirth P q<P.cap (IntegralMixedFramedCompanionQueryBits.root q))
    (hm : IntegralMixedFramedCompanionQueryBits.callerModulus q≤numericCap P (IntegralMixedFramedCompanionQueryBits.root q)) :
    (IntegralMixedFramedNativeBits.machine P a D H h).model (query P D q)=value P D H q := by
  have HA := IntegralMixedFramedNativeBits.producer_actual P a D H h _ (fun _ _ => rfl)
  have HX : get P .slot15 (query P D q)≤4 := by rw [query_get]; exact IntegralMixedFramedCompanionQueryBits.query_context_le P D q
  have HC : get P .slot15 (query P D q)=
      (IntegralMixedFramedHistoryFamilyBits.instruction P D (IntegralMixedVirtualTaskBits.saved P (query P D q))).command.context := by
    rw [query_get,query_saved]
    exact IntegralMixedFramedCompanionQueryBits.query_actual_context P D q
  rw [HA.leading _ (query_valid P D q hb) (query_routine P D q) HX (query_phase P D q),
    IntegralMixedFramedProducerActualBits.leading_actual P D H _ HC,query_modulus P D q hm]
  unfold value
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))
  rw [query_saved]
  exact leading_congr P D H _ _ (IntegralMixedFramedCompanionQueryBits.query_saved_root P D q)
    (IntegralMixedFramedCompanionQueryBits.query_saved_birth P D q)

end LeanCanny.Algebra.IntegralMixedFramedLeadingBits
