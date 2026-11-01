/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMacaulaySnapshot
public import LeanCanny.Computation.NativeTwoCallBranch

/-! # Native negative Gram products from two current actual row entries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramProductNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps IntegralMixedValueGramProductTasks
open scoped Classical
attribute [local irreducible] ArithmeticBits.negate BinaryNat.mulMod

def post (P : Parameters) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNatCode.encode (modulus P (pairFst z)))
    (BinaryNat.mulMod (pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))))

theorem post_FP (P : Parameters) (a : Access P) : post P ∈ FP := by
  have HMB : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HM := HMB.bits_mem_FP
  exact mem_FP_comp (mem_FP_pair HM (mem_FP_comp (mem_FP_pair HM pairSnd_mem_FP) BinaryNat.mulMod_mem_FP))
    ArithmeticBits.negate_mem_FP

theorem post_integer (P : Parameters) (q : List Bool) (x y : ℤ) :
    post P (pair q (pair (residueBits (x : ZMod (modulus P q))) (residueBits (y : ZMod (modulus P q))))) =
      residueBits ((-(x * y) : ℤ) : ZMod (modulus P q)) := by
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  simp only [post, pairFst_pair, pairSnd_pair]
  rw [ArithmeticBits.mulMod_residueBits, ArithmeticBits.negate_residueBits]
  simp only [Int.cast_neg, Int.cast_mul]

noncomputable def factor (P : Parameters) (F : Family) (left : Bool) (q : List Bool) : ℤ :=
  IntegralMixedValueMacaulaySnapshot.pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
    (sourceRow P F q) (column P left q) (row P F left q) (col P F left q)
noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits ((-(factor P F true q * factor P F false q) : ℤ) : ZMod (modulus P q))

noncomputable def right (P : Parameters) (F : Family) (z : List Bool) : List Bool := query P F false (pairFst z)
theorem right_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : right P F ∈ FP :=
  mem_FP_comp pairFst_mem_FP (query_FP P a F h false)

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ left, reply (query P F left q) = IntegralMixedValueMacaulayMatrix.value P F (query P F left q)

theorem result (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : RepliesAt P F reply q) :
    DependentTwoCall.result (query P F true) (right P F) (post P) reply q = value P F q := by
  unfold DependentTwoCall.result
  simp only [right, pairFst_pair]
  rw [he false, he true, IntegralMixedValueMacaulaySnapshot.product_child,
    IntegralMixedValueMacaulaySnapshot.product_child]
  exact post_integer P q _ _

def Selected (P : Parameters) (q : List Bool) : Prop :=
  valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧ isPhase .criticalCoefficient q
noncomputable instance (P : Parameters) (q : List Bool) : Decidable (Selected P q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected_FP (P : Parameters) (a : Access P) : FPPred (Selected P) :=
  (valid_FP P a).and (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2)).and
    (isPhase_FP .criticalCoefficient))

def replyBound (P : Parameters) (q : List Bool) : ℕ := (modulus P q).size
theorem replyBound_unary (P : Parameters) (a : Access P) : UnaryFn (replyBound P) :=
  (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofTwoCalls (query P F true) (right P F) (post P) (query_FP P a F h true) (right_FP P a F h) (post_FP P a)
    (fun q => decide (Selected P q)) (selected_FP P a).flag_mem_FP (value P F) (replyBound P) (replyBound_unary P a)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (he : ∀ q, Selected P q → RepliesAt P F reply q) :
    Correct (machine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofTwoCalls_correct
  · intro q hq
    exact result P F reply q (he q (of_decide_eq_true hq))
  · intro q hq
    rw [he q (of_decide_eq_true hq) true, IntegralMixedValueMacaulaySnapshot.product_child]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q _
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    have HS : Selected P q := of_decide_eq_true hq
    rcases DependentTwoCall.requests_cases _ _ _ _ budget q c hc with hl | hr
    · rw [hl]
      exact query_frame P F true q HS.2.1 HS.2.2
    · rw [hr]
      simp only [right, pairFst_pair]
      exact query_frame P F false q HS.2.1 HS.2.2

end LeanCanny.Algebra.IntegralMixedValueGramProductNative
