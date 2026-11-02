/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionEntry
/-! # Creating-companion packets agree with complete native replies

The modulus bound is explicit. A source modulus that exceeds the fixed task
cap is never replaced by its clipped value.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
attribute [local irreducible] PaddedIntegralGeneratorSource.Source.matrix
  IntegralMixedFramedCompanionBits.entry IntegralMixedFramedCompanionBits.value

theorem query_source_value (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hb : sourceBirth P q<P.cap (root q)) (hm : callerModulus q≤numericCap P (root q)) :
    IntegralMixedFramedCompanionBits.value P D H (query P D q)=
      PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  rw [IntegralMixedFramedCompanionBits.value_entry,IntegralMixedFramedCompanionBits.source_value_entry,
    query_modulus P D q hm,query_row P D q hb,query_col P D q hb]
  apply congrArg (fun z : ℤ => residueBits (z : ZMod (callerModulus q)))
  rw [IntegralMixedFramedCompanionBits.entry_congr P D H _ _ (query_saved_root P D q) (query_saved_birth P D q)]
  exact IntegralMixedFramedCompanionBits.entry_mod P D H _ _ _

theorem model_query_value (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : IntegralMixedFramedNativeBits.Controls P D H)
    (q : List Bool) (hb : sourceBirth P q<P.cap (root q)) (hm : callerModulus q≤numericCap P (root q)) :
    (IntegralMixedFramedNativeBits.machine P a D H h).model (query P D q)=
      PaddedIntegralGeneratorSource.value (IntegralMixedFramedCompanionBits.source P D H) q := by
  have HA := IntegralMixedFramedNativeBits.producer_actual P a D H h _ (fun _ _ => rfl)
  rw [HA.companion _ (query_valid P D q hb) (query_routine P D q)
    (query_context_le P D q) (query_phase P D q)]
  rw [IntegralMixedFramedProducerActualBits.companion_actual P D H _
    (query_actual_context P D q) (query_actual_coordinate P D q)]
  exact query_source_value P D H q hb hm

end LeanCanny.Algebra.IntegralMixedFramedCompanionQueryBits
