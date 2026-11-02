/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorReplies
public import LeanCanny.Computation.NativeTwoCallBranch
/-! # Native squarefree entries use only two strictly lower-routine replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedSquarefreeFactorTasks
open scoped Classical
attribute [local irreducible] BinaryNat.mulMod modulus

noncomputable def right (P : Parameters) (z : List Bool) : List Bool := determinant P (pairFst z)
noncomputable def post (P : Parameters) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))
theorem right_FP (P : Parameters) (a : Access P) : right P ∈ FP :=
  mem_FP_comp pairFst_mem_FP (determinant_FP P a)
theorem post_FP (P : Parameters) (a : Access P) : post P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact mem_FP_comp (f := fun z => pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))
    (g := BinaryNat.mulMod) (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) BinaryNat.mulMod_mem_FP

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 4 ∧
    isPhase .relativePower q ∧ IntegralMixedVirtualContextBits.context P q ∧ get P .slot8 q < IntegralMixedPscEntryBits.degree P F q ∧
      get P .row q < IntegralMixedPscEntryBits.rank P F q ∧ get P .col q < IntegralMixedPscEntryBits.rank P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Selected P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 4)).and
      ((isPhase_FP .relativePower).and ((IntegralMixedVirtualContextBits.context_FP P a).and
        (((get_binary P a .slot8).lt (IntegralMixedPscEntryBits.degree_binary P a F h)).and
          (((get_binary P a .row).lt (IntegralMixedPscEntryBits.rank_binary P a F h)).and
            ((get_binary P a .col).lt (IntegralMixedPscEntryBits.rank_binary P a F h)))))))

abbrev RepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  answer (top P F q) = (IntegralMixedVirtualTaskBits.source P F).value (top P F q) ∧
    answer (determinant P q) = IntegralMixedPscUpperBits.characteristicValue P F (determinant P q)

theorem value_at (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (q : List Bool) (hs : Selected P F q) (he : RepliesAt P F answer q) :
    DependentTwoCall.result (top P F) (right P) (post P) answer q = value P F q := by
  unfold DependentTwoCall.result
  simp only [right, pairFst_pair]
  rw [he.2, he.1, top_value P F g q, determinant_value]
  simp only [post, pairFst_pair, pairSnd_pair, IntegralMixedPscUpperBits.characteristicValue, value,
    product_integer P F q hs.2.2.2.2.2.1 hs.2.2.2.2.2.2, Int.cast_mul]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  exact ArithmeticBits.mulMod_residueBits _ _ _

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofTwoCalls (top P F) (right P) (post P) (top_FP P a F h) (right_FP P a) (post_FP P a)
    (fun q => decide (Selected P F q)) (selected_FP P a F h).flag_mem_FP (value P F)
    (IntegralCriticalHistoryEvaluator.residueWidth P) (IntegralCriticalHistoryEvaluator.residueWidth_unary P a)

attribute [local irreducible] value

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (he : ∀ q, Selected P F q → RepliesAt P F (fun q => residueBits (x q)) q) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · intro q hq
    exact value_at P F g _ q (of_decide_eq_true hq) (he q (of_decide_eq_true hq))
  · intro q _
    exact (IntegralCriticalHistoryEvaluator.answer_length P x (top P F q)).trans_eq
      (congrArg (fun r => (numericCap P r).size) (top_root P F q))
  · intro q _
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact (value_length P F q).trans (Nat.size_le_size (IntegralCriticalHistoryEvaluator.modulus_le P q))
  · intro q c budget hq hc
    have HS : Selected P F q := of_decide_eq_true hq
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q c hc with hl | hr
    · rw [hl]
      exact top_frame P F q HS.2.1
    · rw [hr]
      simp only [right, pairFst_pair]
      exact determinant_frame P q HS.2.1

end LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
