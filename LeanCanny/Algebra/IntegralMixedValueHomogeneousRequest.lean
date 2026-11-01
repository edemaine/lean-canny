/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueCoordinateChild

/-! # Native flat homogeneous value-row controller

This stage uses the exact homogeneous row guard and actual fresh child
writers. Its coordinate branch requests the already constructed virtual
critical source, at a smaller routine rank. The original-row branch asks
the preceding restored-row stage. No coefficient or matrix evaluator is
an argument to its native computation certificates.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open IntegralMixedValueHomogeneousQueries
open scoped Classical

noncomputable def request (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q)

noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (request P F q) :=
  inferInstanceAs (Decidable (HomogeneousSystemCoefficientRequest.request _ _))

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request q := decide (request P F q)
  query := query P F
  immediate _ := []
  finish := pairSnd

theorem request_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (request P F) :=
  (HomogeneousSystemCoefficientRequest.request_FP _ (controls P a F h)).comp (packet_FP P a)

theorem program_controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (program P F).Controls :=
  ⟨(request_FP P a F h).flag_mem_FP, query_FP P a F h, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (program P F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program P F).certificates (program_controls P a F h)

theorem value_eq (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) :
    (program P F).value reply q = if request P F q then reply (query P F q) else [] := by
  simp only [SingleCall.Program.value, program, decide_eq_true_eq, pairSnd_pair]

theorem packet_value (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) :
    (program P F).value reply q =
      (HomogeneousSystemCoefficientRequest.program (parameters P F)).value
        (fun _ => reply (query P F q)) (packet P q) := by
  by_cases HR : request P F q <;>
    simp_all only [SingleCall.Program.value, program, HomogeneousSystemCoefficientRequest.program, request,
      pairSnd_pair, decide_eq_true_eq, ite_true, ite_false]

theorem value_coordinate (P : Parameters) (F : Family) (h : RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (hr : request P F q) (hz : get P .slot8 q ≠ 0)
    (hc : reply (coordinateTask P F q) = (IntegralMixedVirtualTaskBits.source P F).value (coordinateTask P F q)) :
    (program P F).value reply q =
      residueBits (matrixCoefficient F (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot8 q - 1) (IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F q)
        (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [value_eq, ite_eq_left hr, query, ite_eq_right hz, hc]
  exact IntegralMixedValueTaskBounds.coordinateTask_value_guarded P F h q hr hz

theorem requests_iff (P : Parameters) (F : Family) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) : (program P F).controller.Requests reply budget q c ↔ request P F q ∧ c = query P F q := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]

theorem requests_frame (P : Parameters) (F : Family) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 22)
    (hc : (program P F).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  rw [(requests_iff P F reply budget q c).mp hc |>.2]
  exact query_frame P F q hr hp

def stateBound (P : Parameters) (q : List Bool) : ℕ := 2 * q.length + 4 + (modulus P q).size

theorem stateBound_unary (P : Parameters) (a : Access P) : UnaryFn (stateBound P) := by
  have HM : UnaryFn (fun q => (modulus P q).size) :=
    (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact (((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add (UnaryFn.const 4)).add HM

theorem state_length (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hc : request P F q → ∃ z : ZMod (modulus P q), reply (query P F q) = residueBits z) :
    (SingleCall.encState (((program P F).controller.reference reply)^[t] (SingleCall.Program.initial q))).length ≤
      stateBound P q := by
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  apply (program P F).state_length_of_bound reply q t ((modulus P q).size)
  intro HR
  have HQ : request P F q := of_decide_eq_true HR
  obtain ⟨z, HZ⟩ := hc HQ
  change (reply (query P F q)).length ≤ _
  rw [HZ]
  exact residueBits_length_le _ _

end LeanCanny.Algebra.IntegralMixedValueHomogeneousRequest
