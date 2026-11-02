/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutProbeTask
public import LeanCanny.Algebra.IntegralMixedFramedFullChoiceProbe
/-! # Honest modulus packets also retain the requested finite choice

Only numeric field8 is added to the existing fresh packet. If the new cap
clips an outsize request, the factor is unchanged because clipping remains
above its actual finite creating choice. Caller labels stay explicit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTaskBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedCutProbeTaskBits (parameters original root)
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

def requested (P : Parameters) (q : List Bool) := get P .slot8 (original q)
theorem requested_binary (P : Parameters) (a : Access P) : BinaryFn (requested P) :=
  (get_binary P a .slot8).comp IntegralMixedFramedCutProbeTaskBits.original_FP

def query (P : Parameters) (L F C : List Bool→ℕ) :=
  IntegralMixedValueFieldQuery.query (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.query P L F C)
    .rawFactor .companion .slot8 (requested P)
theorem query_FP (P : Parameters) (a : Access P) (L F C : List Bool→ℕ)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) : query P L F C∈FP :=
  IntegralMixedValueFieldQuery.query_FP _ (IntegralMixedFramedCutProbeTaskBits.access P a L F C hL hF hC)
    _ (IntegralMixedFramedCutProbeTaskBits.query_FP P a L F C hL hF hC) _ _ _ _ (requested_binary P a)

theorem query_root (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) : RankedHistoryTask.root (query P L F C q)=root q :=
  (IntegralMixedValueFieldQuery.query_root _ _ _ _ _ _ q).trans (IntegralMixedFramedCutProbeTaskBits.query_root P L F C q)
theorem query_birth (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    birth (parameters P L F C) (query P L F C q)=birth P (original q) :=
  (IntegralMixedValueFieldQuery.query_birth _ _ _ _ _ _ q).trans (IntegralMixedFramedCutProbeTaskBits.query_birth P L F C q)
theorem query_modulus (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    modulus (parameters P L F C) (query P L F C q)=IntegralMixedFramedCutProbeTaskBits.callerModulus q :=
  (IntegralMixedValueFieldQuery.query_modulus _ _ _ _ _ _ q (by decide)).trans (IntegralMixedFramedCutProbeTaskBits.query_modulus P L F C q)
theorem query_get (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) (f : Field) :
    get (parameters P L F C) f (query P L F C q)=if f=.slot14 then 4 else if f=.slot8 then
      min (requested P q) (numericCap (parameters P L F C) (root q)) else
      get (parameters P L F C) f (IntegralMixedFramedCutProbeTaskBits.query P L F C q) := by
  rw [query,IntegralMixedValueFieldQuery.query_get,IntegralMixedFramedCutProbeTaskBits.query_root]
  rfl

theorem query_saved_base (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q)=
      IntegralMixedVirtualTaskBits.saved (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.query P L F C q) :=
  IntegralMixedValueFieldQuery.query_saved _ _ _ _ _ _ q (by decide)

theorem query_choice (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedRawKindChoiceBits.requested (parameters P L F C) (query P L F C q)=
      min (requested P q) (numericCap (parameters P L F C) (root q)) := by
  unfold IntegralMixedRawKindChoiceBits.requested
  simp only [query_get P L F C q,reduceCtorEq,ite_false,ite_true]

theorem query_coefficient (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hk : IntegralMixedFramedCutProbeTaskBits.coefficient P q<2^P.width (RankedHistoryTask.root (original q))) :
    get (parameters P L F C) .coefficient (query P L F C q)=IntegralMixedFramedCutProbeTaskBits.coefficient P q := by
  simp only [query_get P L F C q,reduceCtorEq,ite_false]
  exact IntegralMixedFramedCutProbeTaskBits.query_coefficient P L F C q hk

theorem query_row (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hr : IntegralMixedFramedCutProbeTaskBits.row q<FixedWidthPolynomial.count (birth P (original q))
      (P.width (RankedHistoryTask.root (original q)))) :
    get (parameters P L F C) .row (query P L F C q)=IntegralMixedFramedCutProbeTaskBits.row q := by
  simp only [query_get P L F C q,reduceCtorEq,ite_false]
  exact IntegralMixedFramedCutProbeTaskBits.query_row P L F C q hr

theorem query_col (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hr : IntegralMixedFramedCutProbeTaskBits.col q<FixedWidthPolynomial.count (birth P (original q))
      (P.width (RankedHistoryTask.root (original q)))) :
    get (parameters P L F C) .col (query P L F C q)=IntegralMixedFramedCutProbeTaskBits.col q := by
  simp only [query_get P L F C q,reduceCtorEq,ite_false]
  exact IntegralMixedFramedCutProbeTaskBits.query_col P L F C q hr

theorem query_saved (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedFramedRootPullback.key pairFst (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))=
      IntegralMixedVirtualTaskBits.saved P (original q) := by
  rw [query,IntegralMixedValueFieldQuery.query_saved _ _ _ _ _ _ q (by decide)]
  exact IntegralMixedFramedCutProbeTaskBits.query_saved P L F C q hc

theorem query_valid (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedVirtualCaps.valid (parameters P L F C) (query P L F C q)↔IntegralMixedVirtualCaps.valid P (original q) := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_birth,query_root]
  simp only [parameters,IntegralMixedFramedNormalizationBits.planned,IntegralMixedFramedRootPullback.parameters,
    Function.comp_apply,root,pairFst_pair]
theorem query_context (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedVirtualContextBits.context (parameters P L F C) (query P L F C q) := by
  unfold IntegralMixedVirtualContextBits.context
  simp only [query_get P L F C q,reduceCtorEq,ite_false]
  exact IntegralMixedFramedCutProbeTaskBits.query_virtual_context P L F C q hc

theorem choice_bound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) :
    IntegralMixedRelativeCuts.choiceIndex ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P (original q)))
      ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P (original q)))≤numericCap (parameters P L F C) (root q) := by
  rw [IntegralMixedFramedFullChoiceProbeBits.choiceIndex_eq]
  have HC:=(IntegralMixedRawKindBits.choice_le (family P D H) (IntegralMixedVirtualTaskBits.saved P (original q))).trans
    ((family P D H).scalar_cap _)
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width] at HC
  exact HC.trans (IntegralMixedFramedCutProbeTaskBits.scalar_bound P L F C q)

end LeanCanny.Algebra.IntegralMixedFramedChoiceProbeTaskBits
