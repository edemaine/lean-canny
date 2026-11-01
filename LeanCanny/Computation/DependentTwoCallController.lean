/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.TwoCallController
/-! # Two native recursive calls with an adaptive second query

The second task can use the first reply, as needed when a trailing-index
scan selects a later coefficient query. Both replies remain charged calls.
-/
@[expose] public section
namespace LeanCanny.Computation.DependentTwoCall
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

def query (left right : List Bool → List Bool) (s : RecursiveFold.State) : List Bool :=
  if s.2.1 = 0 then left s.1 else right (pair s.1 s.2.2)

def controller (left right post : List Bool → List Bool) :=
  { (TwoCall.program left (fun _ => []) post).controller with query := query left right }

def queryPacket (left right : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (BoundedFold.counter p) = 0 then left (pairFst p)
  else right (pair (pairFst p) (BoundedFold.accumulator p))

theorem queryPacket_FP (left right : List Bool → List Bool) (hl : left ∈ FP) (hr : right ∈ FP) : queryPacket left right ∈ FP :=
  ((BinaryFn.fromBits BoundedFold.counter_mem_FP).eq (BinaryFn.const 0)).ite_mem_FP
    (mem_FP_comp pairFst_mem_FP hl)
    (mem_FP_comp (mem_FP_pair pairFst_mem_FP BoundedFold.accumulator_mem_FP) hr)

theorem certificates (left right post : List Bool → List Bool) (hl : left ∈ FP) (hr : right ∈ FP) (hp : post ∈ FP) :
    (controller left right post).Certificates (encQ := encBits) (encS := RecursiveFold.encState) := by
  have H := TwoCall.certificates left (fun _ => []) post hl (constFn_mem_FP []) hp
  refine { H with query := ?_ }
  change ComputableTidilyInPolySpace
    (fun s : RecursiveFold.State => if s.2.1 = 0 then left s.1 else right (pair s.1 s.2.2)) RecursiveFold.encState encBits
  have HQ := ComputableTidilyInPolySpace.of_polyTime (FP.computable (queryPacket_FP left right hl hr))
  have HB := ComputableTidilyInPolySpace.of_polyTime BoundedFold.packet_polyTime
  have HE := HQ.comp HB
  simpa only [controller, query, RecursiveFold.encState, TidyBoundedFold.encPacket, queryPacket, BoundedFold.counter_packet, BoundedFold.accumulator_packet, BoundedFold.context_packet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] using HE

def result (left right post answer : List Bool → List Bool) (q : List Bool) : List Bool :=
  post (pair q (pair (answer (left q)) (answer (right (pair q (answer (left q)))))))

theorem reference_zero (left right post answer : List Bool → List Bool) (q : List Bool) :
    (controller left right post).reference answer (q, 0, []) = (q, 1, answer (left q)) := by
  simp only [RecursiveController.Controller.reference, controller, RecursiveFold.Program.controller, TwoCall.program,
    query, show ¬ (2 : ℕ) ≤ 0 from by decide, decide_false, Bool.false_eq_true, ite_false, ite_true]
  simp only [TwoCall.finish, pairFst_pair, pairSnd_pair, BoundedFold.counter_packet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]

theorem reference_one (left right post answer : List Bool → List Bool) (q : List Bool) :
    (controller left right post).reference answer (q, 1, answer (left q)) = (q, 2, result left right post answer q) := by
  simp only [RecursiveController.Controller.reference, controller, RecursiveFold.Program.controller, TwoCall.program,
    query, show ¬ (2 : ℕ) ≤ 1 from by decide, show ¬ (1 : ℕ) = 0 from by decide,
    decide_false, Bool.false_eq_true, ite_false, ite_true]
  simp only [TwoCall.finish, pairFst_pair, pairSnd_pair, BoundedFold.counter_packet, BoundedFold.accumulator_packet, BoundedFold.context_packet,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, show ¬ (1 : ℕ) = 0 from by decide, ite_false]
  rfl

theorem reference_final (left right post answer : List Bool → List Bool) (q : List Bool) :
    (controller left right post).reference answer (q, 2, result left right post answer q) =
      (q, 2, result left right post answer q) := by
  simp only [RecursiveController.Controller.reference, controller, RecursiveFold.Program.controller, TwoCall.program,
    le_refl, decide_true, ite_true]

theorem iterate_two_add (left right post answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    ((controller left right post).reference answer)^[t + 2] ((controller left right post).initial q) =
      (q, 2, result left right post answer q) := by
  induction t with
  | zero =>
    change (controller left right post).reference answer
      ((controller left right post).reference answer (q, 0, [])) = _
    rw [reference_zero, reference_one]
  | succ t ih =>
    rw [show t + 1 + 2 = (t + 2) + 1 by omega, Function.iterate_succ_apply', ih, reference_final]

theorem halted_after (left right post answer : List Bool → List Bool) (q : List Bool) :
    (controller left right post).halted (((controller left right post).reference answer)^[2]
      ((controller left right post).initial q)) = true := by
  rw [show 2 = 0 + 2 from rfl, iterate_two_add]
  rfl

theorem output_when_halted (left right post answer : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (hh : (controller left right post).halted (((controller left right post).reference answer)^[t]
      ((controller left right post).initial q)) = true) :
    (controller left right post).output (((controller left right post).reference answer)^[t]
      ((controller left right post).initial q)) = result left right post answer q := by
  rcases t with _ | (_ | t)
  · cases hh
  · change (controller left right post).halted ((controller left right post).reference answer (q, 0, [])) = true at hh
    rw [reference_zero] at hh
    cases hh
  · rw [show t + 1 + 1 = t + 2 by omega, iterate_two_add]
    rfl

theorem state_length (left right post answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((controller left right post).reference answer)^[t]
      ((controller left right post).initial q))).length ≤
        2 * q.length + 2 * (encNat 2).length + max (answer (left q)).length (result left right post answer q).length + 2 := by
  rcases t with _ | (_ | t)
  · change (RecursiveFold.encState (q, 0, [])).length ≤ _
    rw [RecursiveFold.Program.state_length]
    have H := ComputableTidilyInO.length_encNat_mono (by decide : 0 ≤ 2)
    simp only [List.length_nil]
    omega
  · change (RecursiveFold.encState ((controller left right post).reference answer (q, 0, []))).length ≤ _
    rw [reference_zero, RecursiveFold.Program.state_length]
    have H := ComputableTidilyInO.length_encNat_mono (by decide : 1 ≤ 2)
    omega
  · rw [show t + 1 + 1 = t + 2 by omega, iterate_two_add, RecursiveFold.Program.state_length]
    omega

theorem requests_cases (left right post answer : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hc : (controller left right post).Requests answer budget q c) :
    c = left q ∨ c = right (pair q (answer (left q))) := by
  obtain ⟨t, _, hh, _, he⟩ := hc
  rcases t with _ | (_ | t)
  · exact Or.inl he
  · change c = (controller left right post).query ((controller left right post).reference answer (q, 0, [])) at he
    rw [reference_zero] at he
    exact Or.inr he
  · rw [show t + 1 + 1 = t + 2 by omega, iterate_two_add] at hh
    cases hh

end LeanCanny.Computation.DependentTwoCall
