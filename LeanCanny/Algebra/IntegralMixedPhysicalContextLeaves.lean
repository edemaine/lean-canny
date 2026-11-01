/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalLowReplyMatching
/-! # Physical-context current leaf and monomial machines

Selection includes literal producer context one. Correctness therefore
needs replies only for current physical tasks, never for virtual contexts.
All controllers, state encodings, clocks, and bounds are the native concrete
ones; the additional context test is a native immutable field read.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
open IntegralMixedPhysicalNativeLowerBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 1 ∧
    isPhase p q ∧ get P .slot15 q = 1)

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 1)).and
      ((isPhase_FP p).and ((get_binary P a .slot15).eq (BinaryFn.const 1))))).flag_mem_FP

theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedPhysicalNativeLowerBits.selectedValid P p q = true ∧ get P .slot15 q = 1 := by
  simp only [selected, decide_eq_true_eq, IntegralMixedPhysicalNativeLowerBits.selectedValid_iff]
  tauto

theorem selected_raw (P : Parameters) (p : Phase) (q : List Bool) (hq : selected P p q = true) :
    IntegralMixedPhysicalNativeLowerBits.selectedValid P p q = true := ((selected_iff P p q).mp hq).1

noncomputable def originalMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : Machine :=
  ofSingleCall (originalProgram P F) (original_certificates P a F h ha)
    (selected P .originalCoefficient) (selected_FP P a .originalCoefficient) (original P F) (fun _ => 0) (UnaryFn.const 0)

theorem original_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (reply : List Bool → List Bool) :
    Correct (originalMachine P a F h ha) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q _; rfl
  · intro q _ hr; cases hr
  · intro q c budget _ hc
    obtain ⟨hr, _⟩ := ((originalProgram P F).requests_iff reply budget q c).mp hc
    cases hr

noncomputable def derivativeMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (derivativeProgram P F)
    ((derivativeProgram P F).certificates (IntegralCriticalFlatDerivativeBits.controls P a (derivativeSource P F) (derivativeAccess P a F h)))
    (derivativeInput P F) (IntegralCriticalFlatDerivativeBits.input_FP P a (derivativeSource P F) (derivativeAccess P a F h))
    (selected P .derivativeCoefficient) (selected_FP P a .derivativeCoefficient)
    (IntegralMixedPhysicalCoefficientBits.derivative P F) (replyBound P) (replyBound_unary P a)

theorem derivative_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .derivativeCoefficient q = true → DerivativeRepliesAt P F reply q) :
    Correct (derivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  classical
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact derivative_value_at P a F h g reply q (he q hq)
  · intro q hq hr
    have HH : IntegralDerivativeBits.flatRequest (derivativeSource P F) (derivativeInput P F q) := of_decide_eq_true hr
    have HC := he q hq HH
    have HO : IntegralDerivativeBits.original (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)) = q :=
      (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
    have HM : modulus P (IntegralCriticalFlatDerivativeQuery.writer P
        (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q))) = modulus P q :=
      (IntegralCriticalFlatDerivativeQuery.writer_modulus P _).trans (congrArg (modulus P) HO)
    change (reply (IntegralCriticalFlatDerivativeQuery.writer P
      (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)))).length ≤ replyBound P q
    rw [HC]
    exact (original_length P F _).trans_eq (congrArg Nat.size HM)
  · intro q c budget hq hc
    exact derivative_requests_frame P (derivativeSource P F) reply budget q c
      ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .derivativeCoefficient q).mp (selected_raw P .derivativeCoefficient q hq)).2.2 hc

noncomputable def heightMachine (P : Parameters) (a : Access P) (F : Family) : Machine :=
  ofSingleCall (heightProgram P) (height_certificates P a) (selected P .clearedHeight) (selected_FP P a .clearedHeight)
    (height P F) (replyBound P) (replyBound_unary P a)

theorem height_correct (P : Parameters) (a : Access P) (F : Family) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .clearedHeight q = true →
      reply (IntegralMixedScalarQueryBits.virtualHeight P q) = height P F (IntegralMixedScalarQueryBits.virtualHeight P q)) :
    Correct (heightMachine P a F) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hq
    simpa only [SingleCall.Program.value, heightProgram, ite_true, pairSnd_pair] using
      (he q hq).trans (height_scalar_child P F q)
  · intro q hq _
    change (reply (IntegralMixedScalarQueryBits.virtualHeight P q)).length ≤ replyBound P q
    rw [he q hq, height_scalar_child, IntegralMixedPhysicalNativeLowerBits.height_eq]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    have HR := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .clearedHeight q).mp (selected_raw P .clearedHeight q hq)).2.1
    have HC := ((heightProgram P).requests_iff reply budget q c).mp hc
    have HE : c = IntegralMixedScalarQueryBits.virtualHeight P q := HC.2
    apply Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) HE)
    exact IntegralMixedScalarQueryBits.scalar_frame P .factorPower q (by rw [HR]; decide)

noncomputable def monomialMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (monomialProgram P F)
    ((monomialProgram P F).certificates (IntegralMixedVirtualMonomialRequestBits.controls _ (monomialAccess P a F h) _ _ _
      (IntegralCriticalFlatGenericMonomialBits.coefficientTask_FP P a)
      (IntegralCriticalFlatFactorQuery.writer_FP P a .clearedHeight)
      (IntegralMixedScalarQueryBits.scalarQuery_FP P a .derivativeCoefficient)))
    (monomialInput P F) (IntegralCriticalFlatGenericMonomialBits.input_FP P a (monomialSource P F) (monomialAccess P a F h))
    (selected P .monomialFactor) (selected_FP P a .monomialFactor)
    (IntegralMixedPhysicalFactorBits.monomial P F) (replyBound P) (replyBound_unary P a)

theorem monomial_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .monomialFactor q = true → MonomialRepliesAt P F reply q) :
    Correct (monomialMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact monomial_value_at P a F h g reply q (he q hq)
  · intro q hq hr
    have HV := monomial_value_at P a F h g reply q (he q hq)
    simp only [SingleCall.Program.value, hr, ite_true] at HV
    change pairSnd (pair _ _) = _ at HV
    rw [pairSnd_pair] at HV
    change (reply ((monomialProgram P F).query (monomialInput P F q))).length ≤ replyBound P q
    rw [HV]
    obtain ⟨z, hz⟩ := monomial_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    have HQ := (IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .monomialFactor q).mp (selected_raw P .monomialFactor q hq)
    exact monomial_requests_frame P (monomialSource P F) reply budget q c HQ.2.1 HQ.2.2 hc

end LeanCanny.Algebra.IntegralMixedPhysicalContextBits
