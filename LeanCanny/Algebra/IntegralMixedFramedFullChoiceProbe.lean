/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedLimitChoice
public import LeanCanny.Algebra.IntegralMixedFramedFullCutProbe
/-! # All four full-factor classes admit native finite-choice probes

Outsize query choices are clipped inside the reader; the eventual finite
validity predicate retains its original choice guard. Every query still
uses the same actual saved parent and current-Q arithmetic model.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep
variable {n : ℕ} {P : SpatialSource n}
theorem atChoice_above (r : Rule n) (c : Kind P r) (k : ℕ) (hk : choiceIndex r c≤k) : atChoice r c k=c := by
  cases c <;> simp only [choiceIndex] at hk <;> simp only [atChoice,min_eq_right hk]
theorem atChoice_clipped (r : Rule n) (c : Kind P r) (k b : ℕ) (hb : choiceIndex r c≤b) :
    atChoice r c (min k b)=atChoice r c k := by
  cases c <;> simp only [choiceIndex] at hb <;> simp only [atChoice,min_assoc,min_eq_right hb]
end LeanCanny.Algebra.IntegralMixedRelativeCuts

namespace LeanCanny.Algebra.IntegralMixedFramedFullChoiceProbeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family IntegralMixedCutMatrix.coefficientMatrix

theorem choiceIndex_eq (F : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRelativeCuts.choiceIndex (F.rule key) (F.kind key)=IntegralMixedRawKindBits.choice F key := by
  cases hc : F.kind key <;> simp only [IntegralMixedRelativeCuts.choiceIndex,IntegralMixedRawKindBits.choice,hc]

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  if IntegralMixedFramedFullCutProbeBits.Active P q then residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    (IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state (IntegralMixedVirtualTaskBits.saved P q))
      ((family P D H).birth_bound _) ((family P D H).rule _)
      (IntegralMixedRelativeCuts.atChoice ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
        ((family P D H).kind _) (IntegralMixedRawKindChoiceBits.requested P q)) (get P .coefficient q))
    (get P .row q) (get P .col q) : ZMod (modulus P q)) else []

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCurrentQNativeBits.Controls P D H) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D H h) :
    SpaceFunction (value P D H) := by
  let k:=IntegralMixedFramedNormalizationBits.kind P a D H h.normalization
  have HT : BinaryFn (fun q=>IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    k.tag.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  have HC : FPPred (fun q=>IntegralMixedRawKindChoiceBits.requested P q≤
      IntegralMixedRawKindBits.choice (family P D H) (IntegralMixedVirtualTaskBits.saved P q)) :=
    (get_binary P a .slot8).le (k.choice.comp (IntegralMixedVirtualTaskBits.saved_FP P a))
  have EC:=IntegralMixedFramedChoicePreparedBits.coordinate_evaluator P a D H h hb
  have ES:=IntegralMixedFramedChoicePreparedBits.squarefree_evaluator P a D H h hb
  have EV:=IntegralMixedFramedChoicePreparedBits.value_evaluator P a D H h hb
  have EL:=IntegralMixedFramedLimitChoiceBits.evaluator P a D H h hb
  have EA:=IntegralMixedFramedFullCutProbeBits.currentQ_evaluator P a D H h hb
  have E := SpaceFunction.branch (fun q=>decide (IntegralMixedFramedFullCutProbeBits.Active P q))
    (IntegralMixedFramedFullCutProbeBits.active_FP P a).flag_mem_FP
    (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindChoiceBits.requested P q≤IntegralMixedRawKindBits.choice (family P D H) (IntegralMixedVirtualTaskBits.saved P q)))
      HC.flag_mem_FP
      (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=2))
        (HT.eq (BinaryFn.const 2)).flag_mem_FP EC
        (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=3))
          (HT.eq (BinaryFn.const 3)).flag_mem_FP ES
          (SpaceFunction.branch (fun q=>decide (IntegralMixedRawKindBits.tag (family P D H) (IntegralMixedVirtualTaskBits.saved P q)=4))
            (HT.eq (BinaryFn.const 4)).flag_mem_FP EV EL))) EA) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply E.congr
  funext q
  simp only [value,decide_eq_true_eq]
  by_cases ha : IntegralMixedFramedFullCutProbeBits.Active P q
  · simp only [ha,ite_true]
    split_ifs with hc ht2 ht3 ht4
    · exact IntegralMixedFramedChoicePreparedBits.coordinate_entry P D H q ⟨ha.1,ha.2,ht2,hc⟩
    · exact IntegralMixedFramedChoicePreparedBits.squarefree_entry P D H q ⟨ha.1,ha.2,ht3,hc⟩
    · exact IntegralMixedFramedChoicePreparedBits.value_entry P D H q ⟨ha.1,ha.2,ht4,hc⟩
    · have HB:=IntegralMixedRawKindBits.tag_bounds (family P D H) (IntegralMixedVirtualTaskBits.saved P q)
      exact IntegralMixedFramedLimitChoiceBits.entry P D H q ⟨ha.1,ha.2,by omega,hc⟩
    · have HC' : IntegralMixedRelativeCuts.choiceIndex ((family P D H).rule (IntegralMixedVirtualTaskBits.saved P q))
          ((family P D H).kind (IntegralMixedVirtualTaskBits.saved P q))≤IntegralMixedRawKindChoiceBits.requested P q := by
        rw [choiceIndex_eq]
        exact Nat.le_of_not_ge hc
      rw [IntegralMixedRelativeCuts.atChoice_above _ _ _ HC']
      exact ite_eq_left ha
  · simp only [ha,ite_false]

end LeanCanny.Algebra.IntegralMixedFramedFullChoiceProbeBits
