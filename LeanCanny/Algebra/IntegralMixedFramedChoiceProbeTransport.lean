/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTask
public import LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientTransport
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeTransport
/-! # Choice queries preserve every old coefficient at the original root

An oversized field can be clipped by the new task cap only above the actual
finite creating choice. The selected factor therefore remains exactly the
same. This proof transports the actual profile and bank, not fresh roots.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTransportBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters original)
open IntegralMixedFramedCutProbeTransportBits (lifted liftedPlan liftedData plan data)
open IntegralMixedFramedChoiceProbeTaskBits (query)
open scoped Classical

theorem coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) (k : ℕ) :
    HEq (IntegralMixedFramedChoiceCoefficientBits.coefficient (parameters P L F C) (plan P D L F C) (data P D H L F C)
      (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
      (IntegralMixedRawKindChoiceBits.requested (parameters P L F C) (query P L F C q)) k)
      (IntegralMixedFramedChoiceCoefficientBits.coefficient P D H (IntegralMixedVirtualTaskBits.saved P (original q))
        (IntegralMixedFramedChoiceProbeTaskBits.requested P q) k) := by
  rw [IntegralMixedFramedChoiceProbeTaskBits.query_choice]
  have HA:=IntegralMixedFramedChoiceCoefficientBits.planned (lifted P) (liftedPlan P D) (liftedData P D H)
    (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
    (min (IntegralMixedFramedChoiceProbeTaskBits.requested P q)
      (numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q))) k
  have HB:=IntegralMixedFramedChoiceCoefficientBits.pullback P D H pairFst IntegralMixedFramedModulusPacket.extra
    (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
    (min (IntegralMixedFramedChoiceProbeTaskBits.requested P q)
      (numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q))) k
  rw [IntegralMixedFramedChoiceProbeTaskBits.query_saved P L F C q hc] at HB
  have HC:=IntegralMixedFramedChoiceCoefficientBits.clipped P D H (IntegralMixedVirtualTaskBits.saved P (original q))
    (IntegralMixedFramedChoiceProbeTaskBits.requested P q)
    (numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q)) k
    (IntegralMixedFramedChoiceProbeTaskBits.choice_bound P D H L F C q)
  exact HA.trans (HB.trans (heq_of_eq HC))

private theorem integerEntry_congr {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (h : m=n) (hM : HEq M N) (r s : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry M r s=IntegralCriticalTotalSnapshotBits.integerEntry N r s := by
  cases h
  cases hM
  rfl

theorem entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) (k r s : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedFramedChoiceCoefficientBits.coefficient (parameters P L F C) (plan P D L F C) (data P D H L F C)
        (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
        (IntegralMixedRawKindChoiceBits.requested (parameters P L F C) (query P L F C q)) k) r s=
    IntegralCriticalTotalSnapshotBits.integerEntry
      (IntegralMixedFramedChoiceCoefficientBits.coefficient P D H (IntegralMixedVirtualTaskBits.saved P (original q))
        (IntegralMixedFramedChoiceProbeTaskBits.requested P q) k) r s := by
  apply integerEntry_congr _ _ ?_ (coefficient P D H L F C q hc k) r s
  rw [IntegralMixedFramedChoiceProbeTaskBits.query_saved_base]
  exact IntegralMixedFramedCutProbeTransportBits.rank P D H L F C q

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTransportBits
