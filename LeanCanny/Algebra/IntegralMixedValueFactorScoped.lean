/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueFactorNative
public import LeanCanny.Algebra.IntegralMixedGramScopedCurrent
/-! # Value factors request Gram coefficients only in their actual virtual contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueFactorScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedValueFactorTasks IntegralMixedValueFactorValue
open IntegralMixedValueFactorNative
open scoped Classical

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedValueFactorNative.Selected P F q ∧ IntegralMixedVirtualContextBits.context P q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Selected P F) :=
  (IntegralMixedValueFactorNative.selected_FP P a F h).and (IntegralMixedVirtualContextBits.context_FP P a)

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :=
  (IntegralMixedValueFactorNative.machine P a F h).withGuard (fun q => decide (Selected P F q)) (selected_FP P a F h).flag_mem_FP

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (he : ∀ q, Selected P F q → RepliesAt P F answer q) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (program P F).halted_after answer q
  · intro q t hq hh
    have HQ : Selected P F q := of_decide_eq_true hq
    have HS := HQ.1
    exact ((program P F).output_when_halted answer q t hh).trans (value_at P F g answer q HS.1 (he q HQ))
  · intro q t hq
    have HQ : Selected P F q := of_decide_eq_true hq
    have HS := HQ.1
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    apply (program P F).state_length_of_bound answer q t ((modulus P q).size)
    intro hp
    have hk : 0 < (choice P F q).val := of_decide_eq_true hp
    change (answer (query P F q)).length ≤ _
    rw [he q HQ hk, child_value P F g q HS.1 hk]
    exact value_length P F q
  · intro q c budget hq hc
    have HQ : Selected P F q := of_decide_eq_true hq
    have HS := HQ.1
    have HQ := (SingleCall.Program.requests_iff (program P F) answer budget q c).mp hc
    rw [HQ.2]
    exact query_frame P F q HS.2.1

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedGramScopedBits.Matches P F answer)
    (q : List Bool) (hs : Selected P F q) : RepliesAt P F answer q := by
  intro _
  have HV := IntegralMixedValueRowInternalReplies.valid_transport P q _ hs.1.1 (query_root P F q) (query_birth P F q)
  have HR := IntegralMixedValueFieldQuery.query_routine P (first P F) .pscDeterminant .relativePower .col (selectedCol P F) q
  have HP := IntegralMixedValueFieldQuery.query_phase P (first P F) .pscDeterminant .relativePower .col (selectedCol P F) q
  change phase (query P F q) = 24 at HP
  have HX : IntegralMixedVirtualContextBits.context P (query P F q) := by
    unfold IntegralMixedVirtualContextBits.context
    simpa only [IntegralMixedVirtualContextBits.context, query_get P F g q hs.1.1, reduceCtorEq, ite_false] using hs.2
  have H := own _ HV HR (Or.inr (Or.inr (Or.inr (Or.inr HP)))) HX
  rw [HP] at H
  exact H

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (own : IntegralMixedGramScopedBits.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g answer (fun q hs => replies_of_matches P F g answer own q hs)

end LeanCanny.Algebra.IntegralMixedValueFactorScopedBits
