/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinateProfile
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTask
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeTransport
/-! # Unrestricted coordinate packets preserve the actual coefficient matrix

The independent Y and E selectors retain the original old scalar algebra.
The cap conditions are explicit; no equality between unrelated roots or
arbitrary source-equality premise is needed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTransportBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters original)
open IntegralMixedFramedCutProbeTransportBits (lifted liftedPlan liftedData plan data)
open IntegralMixedFramedAllCoordinateTaskBits (query coordinate)
open scoped Classical

theorem coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hc : IntegralMixedVirtualContextBits.context P (original q))
    (hj : coordinate P q≤numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q))
    (hy : IntegralMixedFramedChoiceProbeTaskBits.requested P q≤numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q)) (k : ℕ) :
    HEq (IntegralMixedFramedAllCoordinateBits.coefficient (parameters P L F C) (plan P D L F C) (data P D H L F C)
      (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
      (get (parameters P L F C) .slot13 (query P L F C q)) (get (parameters P L F C) .slot8 (query P L F C q)) k)
      (IntegralMixedFramedAllCoordinateBits.coefficient P D H (IntegralMixedVirtualTaskBits.saved P (original q))
        (coordinate P q) (IntegralMixedFramedChoiceProbeTaskBits.requested P q) k) := by
  rw [IntegralMixedFramedAllCoordinateTaskBits.query_coordinate P L F C q hj,
    IntegralMixedFramedAllCoordinateTaskBits.query_choice P L F C q hy]
  have HA:=IntegralMixedFramedAllCoordinateBits.planned (lifted P) (liftedPlan P D) (liftedData P D H)
    (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
    (coordinate P q) (IntegralMixedFramedChoiceProbeTaskBits.requested P q) k
  have HB:=IntegralMixedFramedAllCoordinateBits.pullback P D H pairFst IntegralMixedFramedModulusPacket.extra
    (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
    (coordinate P q) (IntegralMixedFramedChoiceProbeTaskBits.requested P q) k
  rw [IntegralMixedFramedAllCoordinateTaskBits.query_saved P L F C q hc] at HB
  exact HA.trans HB

private theorem integerEntry_congr {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (h : m=n) (hM : HEq M N) (r s : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry M r s=IntegralCriticalTotalSnapshotBits.integerEntry N r s := by
  cases h
  cases hM
  rfl

theorem entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hc : IntegralMixedVirtualContextBits.context P (original q))
    (hj : coordinate P q≤numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q))
    (hy : IntegralMixedFramedChoiceProbeTaskBits.requested P q≤numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q)) (k r s : ℕ) :
    IntegralMixedCoordinateCoefficientSnapshot.coefficient (family (parameters P L F C) (plan P D L F C) (data P D H L F C))
      (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
      (get (parameters P L F C) .slot13 (query P L F C q)) (get (parameters P L F C) .slot8 (query P L F C q)) k r s=
    IntegralMixedCoordinateCoefficientSnapshot.coefficient (family P D H) (IntegralMixedVirtualTaskBits.saved P (original q))
      (coordinate P q) (IntegralMixedFramedChoiceProbeTaskBits.requested P q) k r s := by
  apply integerEntry_congr _ _ ?_ (coefficient P D H L F C q hc hj hy k) r s
  rw [IntegralMixedFramedAllCoordinateTaskBits.query_saved_base]
  exact IntegralMixedFramedCutProbeTransportBits.rank P D H L F C q

end LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTransportBits
