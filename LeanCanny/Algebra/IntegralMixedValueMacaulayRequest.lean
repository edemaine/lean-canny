/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueReciprocalSnapshot
public import LeanCanny.Algebra.MacaulayIntegralLocalCorrect

/-! # Native value Macaulay controller with explicit integral-basis validity

The active source requests one actual mapped-system coefficient. Padding
uses an identity entry at equal valid basis labels, including nonzero
labels. Out-of-range basis labels are rejected before requesting a child
or emitting a padding identity.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueMacaulayRequest
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps IntegralMixedValueMacaulayTasks
open scoped Classical

def BasisValid (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  get P .row q < count ((IntegralMixedVirtualTaskBits.family P F).birth q + 2) ((IntegralMixedVirtualTaskBits.family P F).width q) ∧
  get P .col q < count ((IntegralMixedVirtualTaskBits.family P F).birth q + 2) ((IntegralMixedVirtualTaskBits.family P F).width q)
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (BasisValid P F q) :=
  inferInstanceAs (Decidable (_ ∧ _))

noncomputable def request (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  BasisValid P F q ∧ MacaulayIntegralEntryRequest.request (layout P F) (packet P q)
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (request P F q) :=
  inferInstanceAs (Decidable (_ ∧ _))

noncomputable def immediate (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if BasisValid P F q then MacaulayIntegralEntryRequest.immediate (layout P F) (modulus P) (packet P q) else []

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request q := decide (request P F q)
  query := query P F
  immediate := immediate P F
  finish := pairSnd

theorem basisValid_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (BasisValid P F) := by
  have H := IntegralMixedVirtualTaskBits.metadata P a F h
  have HR := ((BinaryFn.const 2).powUnary H.width).powUnary (H.birth.add (UnaryFn.const 2))
  exact ((get_binary P a .row).lt HR).and ((get_binary P a .col).lt HR)
theorem request_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (request P F) :=
  (basisValid_FP P a F h).and
    ((MacaulayIntegralEntryRequest.request_FP _ (layout_controls P a F h)).comp (packet_FP P a))
attribute [local irreducible] MacaulayIntegralEntryRequest.immediate
theorem immediate_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : immediate P F ∈ FP := by
  have HG : MacaulayIntegralEntryRequest.immediate (layout P F) (modulus P) ∈ FP :=
    MacaulayIntegralEntryRequest.immediate_FP (layout P F) (layout_controls P a F h) (modulus P) (modulus_binary P a)
  have HI : (fun q => MacaulayIntegralEntryRequest.immediate (layout P F) (modulus P) (packet P q)) ∈ FP :=
    mem_FP_comp (f := packet P) (g := MacaulayIntegralEntryRequest.immediate (layout P F) (modulus P))
      (packet_FP P a) HG
  have HE := (basisValid_FP P a F h).ite_mem_FP HI (constFn_mem_FP [])
  exact mem_FP_of_eq HE (fun _ => rfl)
theorem program_controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (program P F).Controls :=
  ⟨(request_FP P a F h).flag_mem_FP, query_FP P a F h, immediate_FP P a F h, pairSnd_mem_FP⟩
theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    (program P F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program P F).certificates (program_controls P a F h)

theorem value_eq (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) :
    (program P F).value reply q = if request P F q then reply (query P F q) else immediate P F q := by
  simp only [SingleCall.Program.value, program, decide_eq_true_eq, pairSnd_pair]

theorem packet_value (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) (hb : BasisValid P F q) :
    (program P F).value reply q =
      (MacaulayIntegralEntryRequest.program (layout P F) (modulus P)).value
        (fun _ => reply (query P F q)) (packet P q) := by
  by_cases HR : MacaulayIntegralEntryRequest.request (layout P F) (packet P q) <;>
    simp_all only [SingleCall.Program.value, program, MacaulayIntegralEntryRequest.program, request, immediate,
      pairSnd_pair, decide_eq_true_eq, and_self, and_false, ite_true, ite_false]

theorem basis_invalid (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (hb : ¬BasisValid P F q) : (program P F).value reply q = [] := by
  rw [value_eq, ite_eq_right (fun H => hb H.1), immediate, ite_eq_right hb]

theorem requests_iff (P : Parameters) (F : Family) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) : (program P F).controller.Requests reply budget q c ↔ request P F q ∧ c = query P F q := by
  rw [SingleCall.Program.requests_iff]
  simp only [program, decide_eq_true_eq]
theorem requests_frame (P : Parameters) (F : Family) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 24)
    (hc : (program P F).controller.Requests reply budget q c) : IntegralMixedRoutineTaskBits.Frame P q c := by
  rw [((requests_iff P F reply budget q c).mp hc).2]
  exact query_frame P F q hr hp

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  request P F q → reply (query P F q) = IntegralMixedValueReciprocalMatrix.value P F (query P F q)

theorem state_length (P : Parameters) (F : Family) (g : RootGeometry P F) (reply : List Bool → List Bool)
    (q : List Bool) (t : ℕ) (he : RepliesAt P F reply q) :
    (SingleCall.encState (((program P F).controller.reference reply)^[t] (SingleCall.Program.initial q))).length ≤
      IntegralMixedValueHomogeneousRequest.stateBound P q := by
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  apply (program P F).state_length_of_bound reply q t ((modulus P q).size)
  intro HR
  have HQ : request P F q := of_decide_eq_true HR
  change (reply (query P F q)).length ≤ _
  rw [he HQ, IntegralMixedValueReciprocalSnapshot.macaulay_child P F g q]
  exact residueBits_length_le _ _

end LeanCanny.Algebra.IntegralMixedValueMacaulayRequest
