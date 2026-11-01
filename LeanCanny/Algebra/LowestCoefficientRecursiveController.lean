/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.LowestCoefficientSpace
public import LeanCanny.Computation.RecursiveFoldController
public import LeanCanny.Computation.ControllerPostprocess
/-! # A native trailing-degree scan with charged coefficient-zero requests -/
@[expose] public section
namespace LeanCanny.Algebra.LowestCoefficientBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def program (degree : List Bool → ℕ) (task : List Bool → List Bool) : RecursiveFold.Program where
  count q := degree q + 1
  seed _ := []
  entryTask := task
  finish := LowestCoefficientBits.finish

def controller (degree : List Bool → ℕ) (task : List Bool → List Bool) :=
  (program degree task).controller.postprocess BinaryNat.pred

theorem certificates (degree : List Bool → ℕ) (hd : BinaryFn degree) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller degree task).Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveController.Controller.postprocess_certificates _
    ((program degree task).certificates (hd.add (BinaryFn.const 1)) (constFn_mem_FP []) ht
      LowestCoefficientBits.finish_mem_FP) _ BinaryNat.pred_mem_FP

theorem partialValue_at (degree : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool)
    (zero : ℕ → Bool) (hr : ∀ i < degree q + 1, answer (task (pair q (BinaryNatCode.encode i))) = [zero i])
    (k : ℕ) (hk : k ≤ degree q + 1) :
    (program degree task).partialValue answer q k = scan zero k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (program degree task).update answer
      (BoundedFold.packet q k ((program degree task).partialValue answer q k)) = _
    rw [ih (by omega)]
    simp only [RecursiveFold.Program.update, BoundedFold.update, program, LowestCoefficientBits.finish,
      Function.comp_apply, BoundedFold.query, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet, hr k (by omega), scan, List.cons.injEq, and_true]
    split_ifs <;> simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem halted_after (degree : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) :
    (controller degree task).halted (((controller degree task).reference answer)^[degree q + 1]
      ((controller degree task).initial q)) = true := (program degree task).halted_after answer q

theorem output_when_halted {R : Type*} [Semiring R] (degree : List Bool → ℕ) (task answer : List Bool → List Bool)
    (q : List Bool) (p : Polynomial R) (hd : p.natDegree ≤ degree q)
    (hr : ∀ i < degree q + 1, answer (task (pair q (BinaryNatCode.encode i))) = [decide (p.coeff i = 0)])
    (t : ℕ) (hh : (controller degree task).halted (((controller degree task).reference answer)^[t]
      ((controller degree task).initial q)) = true) :
    (controller degree task).output (((controller degree task).reference answer)^[t]
      ((controller degree task).initial q)) = BinaryNatCode.encode p.natTrailingDegree := by
  change BinaryNat.pred ((program degree task).controller.output (((program degree task).controller.reference answer)^[t]
    ((program degree task).initial q))) = _
  rw [(program degree task).output_when_halted answer q t hh]
  change BinaryNat.pred ((program degree task).partialValue answer q (degree q + 1)) = _
  rw [partialValue_at degree task answer q _ hr _ le_rfl]
  exact scan_eq_trailingDegree p _ (by omega)

def stateBound (degree : List Bool → ℕ) (q : List Bool) : ℕ :=
  2 * q.length + 2 * (encNat (degree q + 1)).length + (degree q + 1).size + 2

theorem stateBound_unary (degree : List Bool → ℕ) (hd : BinaryFn degree) : UnaryFn (stateBound degree) := by
  have HC := hd.add (BinaryFn.const 1)
  have HS : UnaryFn (fun q => (degree q + 1).size) :=
    (UnaryFn.length HC.bits_mem_FP).of_eq (fun q => Nat.size_eq_bits_len _)
  have HL : UnaryFn (fun q => (encNat (degree q + 1)).length) :=
    HS.of_eq (fun q => (length_encNat_eq_size _).symm)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HL)).add HS).add (UnaryFn.const 2)

theorem state_length (degree : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool)
    (zero : ℕ → Bool) (hr : ∀ i < degree q + 1, answer (task (pair q (BinaryNatCode.encode i))) = [zero i]) (t : ℕ) :
    (RecursiveFold.encState (((controller degree task).reference answer)^[t]
      ((controller degree task).initial q))).length ≤ stateBound degree q := by
  apply (program degree task).orbit_length answer q t ((degree q + 1).size)
  intro i hi
  rw [partialValue_at degree task answer q zero hr i hi]
  exact (scan_length_le zero i).trans (Nat.size_le_size hi)

theorem requests_cases (degree : List Bool → ℕ) (task answer : List Bool → List Bool)
    (steps : List Bool → ℕ) (q c : List Bool)
    (hc : (controller degree task).Requests answer steps q c) :
    ∃ i < degree q + 1, c = task (pair q (BinaryNatCode.encode i)) := by
  let P := program degree task
  change P.controller.Requests answer steps q c at hc
  obtain ⟨t, _, hh, _, he⟩ := hc
  have HI : min t (P.count q) < P.count q := by
    rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at hh
    have H : ¬ P.count q ≤ min t (P.count q) := of_decide_eq_false hh
    omega
  refine ⟨min t (P.count q), HI, ?_⟩
  rw [show P.controller.initial q = P.initial q from rfl, P.reference_iterate] at he
  exact he

end LeanCanny.Algebra.LowestCoefficientBits.RecursiveStage
