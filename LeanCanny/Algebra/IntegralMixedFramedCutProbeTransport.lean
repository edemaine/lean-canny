/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeTask
/-! # Full relative-factor matrix entries retain the original parent

Budget planning and an honest modulus-root pullback preserve the entire
selected factor. This includes every coefficient above the stored degree;
natural matrix indices retain their zero-outside convention.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutProbeTransportBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

abbrev lifted (P : Parameters) := IntegralMixedFramedRootPullback.parameters P pairFst IntegralMixedFramedModulusPacket.extra
noncomputable abbrev liftedPlan (P : Parameters) (D : Plan P) :=
  IntegralMixedFramedRootPullback.plan P D pairFst IntegralMixedFramedModulusPacket.extra
noncomputable abbrev liftedData (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedRootPullback.data P D H pairFst IntegralMixedFramedModulusPacket.extra
noncomputable def plan (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ) :
    Plan (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) :=
  IntegralMixedFramedNormalizationBits.plannedPlan (lifted P) (liftedPlan P D) (L∘pairFst) (F∘pairFst) (C∘pairFst)
noncomputable def data (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) :
    IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) (plan P D L F C) :=
  IntegralMixedFramedNormalizationBits.plannedData (lifted P) (liftedPlan P D) (liftedData P D H)
    (L∘pairFst) (F∘pairFst) (C∘pairFst)

theorem coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (IntegralMixedFramedCutProbeTaskBits.original q)) (k : ℕ) :
    HEq ((IntegralMixedFramedCutSourceBits.source (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (plan P D L F C) (data P D H L F C)).coefficient
        (IntegralMixedVirtualTaskBits.saved (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
          (IntegralMixedFramedCutProbeTaskBits.query P L F C q)) k)
      ((IntegralMixedFramedCutSourceBits.source P D H).coefficient
        (IntegralMixedVirtualTaskBits.saved P (IntegralMixedFramedCutProbeTaskBits.original q)) k) := by
  have HA:=IntegralMixedFramedCutPlanning.coefficient (lifted P) (liftedPlan P D) (liftedData P D H)
    (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (IntegralMixedVirtualTaskBits.saved (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTaskBits.query P L F C q)) k
  have HB:=IntegralMixedFramedCutRootPullback.coefficient P D H pairFst IntegralMixedFramedModulusPacket.extra
    (IntegralMixedVirtualTaskBits.saved (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTaskBits.query P L F C q)) k
  rw [IntegralMixedFramedCutProbeTaskBits.query_saved P L F C q hc] at HB
  exact HA.trans HB

theorem rank (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) :
    FixedWidthPolynomial.count
      ((family (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) (plan P D L F C) (data P D H L F C)).birth
        (IntegralMixedVirtualTaskBits.saved (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
          (IntegralMixedFramedCutProbeTaskBits.query P L F C q)))
      ((family (IntegralMixedFramedCutProbeTaskBits.parameters P L F C) (plan P D L F C) (data P D H L F C)).width
        (IntegralMixedVirtualTaskBits.saved (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
          (IntegralMixedFramedCutProbeTaskBits.query P L F C q)))=
    FixedWidthPolynomial.count ((family P D H).birth (IntegralMixedVirtualTaskBits.saved P (IntegralMixedFramedCutProbeTaskBits.original q)))
      ((family P D H).width (IntegralMixedVirtualTaskBits.saved P (IntegralMixedFramedCutProbeTaskBits.original q))) := by
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry _ _ _).birth,
    (IntegralMixedFramedHistoryFamilyBits.geometry _ _ _).width,
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth,
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H).width,
    IntegralMixedFramedCutProbeTaskBits.query_birth,IntegralMixedFramedCutProbeTaskBits.query_root,
    IntegralMixedFramedCutProbeTaskBits.query_width]

private theorem integerEntry_congr {m n : ℕ} (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin n) (Fin n) ℤ)
    (h : m=n) (hM : HEq M N) (r s : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry M r s=IntegralCriticalTotalSnapshotBits.integerEntry N r s := by
  cases h
  cases hM
  rfl

theorem entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (IntegralMixedFramedCutProbeTaskBits.original q)) (k r s : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry
      ((IntegralMixedFramedCutSourceBits.source (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
        (plan P D L F C) (data P D H L F C)).coefficient
        (IntegralMixedVirtualTaskBits.saved (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
          (IntegralMixedFramedCutProbeTaskBits.query P L F C q)) k) r s=
    IntegralCriticalTotalSnapshotBits.integerEntry ((IntegralMixedFramedCutSourceBits.source P D H).coefficient
      (IntegralMixedVirtualTaskBits.saved P (IntegralMixedFramedCutProbeTaskBits.original q)) k) r s :=
  integerEntry_congr _ _ (rank P D H L F C q) (coefficient P D H L F C q hc k) r s

end LeanCanny.Algebra.IntegralMixedFramedCutProbeTransportBits
