/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramSumChildren

/-! # Native negative Gram entry computation from actual product children -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramSumNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch Turing.MultiTapeTM
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open IntegralMixedValueGramSumSource IntegralMixedValueGramSumChildren
open scoped Classical BigOperators

def encodedModulus (P : Parameters) (q : List Bool) : List Bool := BinaryNatCode.encode (modulus P q)
theorem encodedModulus_eq (P : Parameters) : (fun q => Nat.fromBitsLE (encodedModulus P q)) = modulus P := by
  funext q
  exact Nat.fromBitsLE_bits _
noncomputable def program (P : Parameters) (F : Family) :=
  ModularFold.RecursiveStage.sumProgram (programCount P F) (encodedModulus P) (IntegralMixedValueGramSumTasks.query P)

theorem partial_value (P : Parameters) (F : Family) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (hv : valid P q) (he : RepliesAt P F reply q)
    (k : ℕ) (hk : k ≤ programCount P F q) :
    (program P F).partialValue reply q k = residueBits
      (∑ i ∈ Finset.range k, (summand P F q i : ZMod (modulus P q))) :=
  ModularFold.RecursiveStage.sum_partialValueWithModulus _ _ _ reply (modulus P) (encodedModulus_eq P) q
    (fun i => (summand P F q i : ZMod (modulus P q))) (Nat.pos_of_ne_zero (modulus_ne_zero P q))
    (reply_value P F g reply q hv he) k hk

theorem value_at (P : Parameters) (F : Family) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (hv : valid P q) (he : RepliesAt P F reply q) :
    (program P F).value reply q = value P F q := by
  have H := partial_value P F g reply q hv he (programCount P F q) le_rfl
  rw [← Int.cast_sum, sum_eq] at H
  exact H

def Selected (P : Parameters) (q : List Bool) : Prop :=
  valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧ isPhase .companion q
noncomputable instance (P : Parameters) (q : List Bool) : Decidable (Selected P q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected_FP (P : Parameters) (a : Access P) : FPPred (Selected P) :=
  (valid_FP P a).and (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2)).and
    (isPhase_FP .companion))

noncomputable def stateBound (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat (programCount P F q)).length + (modulus P q).size + 2
theorem stateBound_unary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : UnaryFn (stateBound P F) := by
  have HL : UnaryFn (fun q => (encNat (programCount P F q)).length) :=
    (UnaryFn.length (programCount_binary P a F h).bits_mem_FP).of_eq (fun q => by
      simp only [length_encNat_eq_size, Nat.size_eq_bits_len, BinaryNatCode.encode])
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HL)).add
    (IntegralMixedValueGramProductNative.replyBound_unary P a)).add (UnaryFn.const 2)

theorem state_length (P : Parameters) (F : Family) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (hv : valid P q) (he : RepliesAt P F reply q) (t : ℕ) :
    (RecursiveFold.encState (((program P F).controller.reference reply)^[t] ((program P F).initial q))).length ≤
      stateBound P F q := by
  apply (program P F).orbit_length reply q t ((modulus P q).size)
  intro k hk
  rw [partial_value P F g reply q hv he k hk]
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  exact residueBits_length_le _ _

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (program P F).controller
  certificates := ModularFold.RecursiveStage.sum_certificates _ _ _ (programCount_binary P a F h)
    (modulus_binary P a).bits_mem_FP (IntegralMixedValueGramSumTasks.query_FP P a)
  selected q := decide (Selected P q)
  selected_FP := (selected_FP P a).flag_mem_FP
  model := value P F
  clock := programCount P F
  clock_binary := programCount_binary P a F h
  stateBound := stateBound P F
  stateBound_unary := stateBound_unary P a F h

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (he : ∀ q, Selected P q → RepliesAt P F reply q) :
    Correct (machine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (program P F).halted_after reply q
  · intro q t hq hh
    have HS : Selected P q := of_decide_eq_true hq
    exact ((program P F).output_when_halted reply q t hh).trans (value_at P F g reply q HS.1 (he q HS))
  · intro q t hq
    have HS : Selected P q := of_decide_eq_true hq
    exact state_length P F g reply q HS.1 (he q HS) t
  · intro q c budget hq hc
    have HS : Selected P q := of_decide_eq_true hq
    let C := program P F
    change C.controller.Requests reply budget q c at hc
    obtain ⟨t, _, _, _, hc⟩ := hc
    rw [show C.controller.initial q = C.initial q from rfl, C.reference_iterate] at hc
    rw [hc]
    exact IntegralMixedValueGramSumTasks.query_frame P q _ HS.2.1 HS.2.2

end LeanCanny.Algebra.IntegralMixedValueGramSumNative
