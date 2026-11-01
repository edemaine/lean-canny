/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.LowestCoefficientRecursiveController
/-! # Trailing scans accept canonical residue flags

Only equality with `[true]` denotes a zero coefficient. In particular, the
canonical residue zero `[]` can denote a nonzero coefficient; a padded
Boolean encoding is not required.
-/
@[expose] public section
namespace LeanCanny.Algebra.LowestCoefficientBits.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem partialValue_flags (degree : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (k : ℕ) :
    (program degree task).partialValue answer q k =
      scan (fun i => decide (answer (task (pair q (BinaryNatCode.encode i))) = [true])) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (program degree task).update answer
      (BoundedFold.packet q k ((program degree task).partialValue answer q k)) = _
    rw [ih]
    simp only [RecursiveFold.Program.update, BoundedFold.update, program, LowestCoefficientBits.finish,
      Function.comp_apply, BoundedFold.query, pairFst_pair, pairSnd_pair, BoundedFold.context_packet,
      BoundedFold.counter_packet, BoundedFold.accumulator_packet, scan, decide_eq_true_eq,
      BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem scan_congr_bounded (f g : ℕ → Bool) (k : ℕ) (h : ∀ i < k, f i = g i) : scan f k = scan g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [scan, scan, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

theorem output_when_halted_flags {R : Type*} [Semiring R] (degree : List Bool → ℕ) (task answer : List Bool → List Bool)
    (q : List Bool) (p : Polynomial R) (hd : p.natDegree ≤ degree q)
    (hr : ∀ i < degree q + 1, answer (task (pair q (BinaryNatCode.encode i))) = [true] ↔ p.coeff i = 0)
    (t : ℕ) (hh : (controller degree task).halted (((controller degree task).reference answer)^[t]
      ((controller degree task).initial q)) = true) :
    (controller degree task).output (((controller degree task).reference answer)^[t]
      ((controller degree task).initial q)) = BinaryNatCode.encode p.natTrailingDegree := by
  change BinaryNat.pred ((program degree task).controller.output (((program degree task).controller.reference answer)^[t]
    ((program degree task).initial q))) = _
  rw [(program degree task).output_when_halted answer q t hh]
  change BinaryNat.pred ((program degree task).partialValue answer q (degree q + 1)) = _
  rw [partialValue_flags]
  have HS := scan_congr_bounded
    (fun i => decide (answer (task (pair q (BinaryNatCode.encode i))) = [true]))
    (fun i => decide (p.coeff i = 0)) (degree q + 1) (fun i hi => by
      by_cases HX : answer (task (pair q (BinaryNatCode.encode i))) = [true]
      · have HY := (hr i hi).mp HX
        simp only [HX, HY, decide_true]
      · have HY : p.coeff i ≠ 0 := fun H => HX ((hr i hi).mpr H)
        simp only [HX, HY, decide_false])
  rw [HS]
  exact scan_eq_trailingDegree p _ (by omega)

theorem state_length_any (degree : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((controller degree task).reference answer)^[t]
      ((controller degree task).initial q))).length ≤ stateBound degree q := by
  apply (program degree task).orbit_length answer q t ((degree q + 1).size)
  intro i hi
  rw [partialValue_flags]
  exact (scan_length_le _ i).trans (Nat.size_le_size hi)

end LeanCanny.Algebra.LowestCoefficientBits.RecursiveStage
