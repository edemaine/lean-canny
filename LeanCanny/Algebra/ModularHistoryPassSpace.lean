/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ModularHistoryPassFP
public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionChain
/-! # Forward residue tables with charged polynomial-space steps -/
@[expose] public section
namespace LeanCanny.Algebra.ModularHistoryPassSpace
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open ModularHistoryPass
set_option backward.isDefEq.respectTransparency false

structure Access (F : Family) where
  count : UnaryFn F.count
  modulus : BinaryFn F.modulus
  step : List Bool → List Bool
  step_space : SpaceFunction step
  step_eq : ∀ c i (v : List (ZMod (F.modulus c))), v.length = i →
    step (BoundedFold.packet c i (WordList.encode (v.map residueBits))) = residueBits (F.next c i v)

def update (F : Family) (a : Access F) (p : List Bool) : List Bool := pair (a.step p) (BoundedFold.accumulator p)

theorem update_evaluator (F : Family) (a : Access F) : SpaceFunction (update F a) :=
  a.step_space.pairOutputs (SpaceFunction.ofFP _ BoundedFold.accumulator_mem_FP)

theorem fold_encoded (F : Family) (a : Access F) (c : List Bool) (i : ℕ) :
    BoundedFold.fold (update F a) (fun _ => []) c i = WordList.encode ((F.values c i).map residueBits) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [BoundedFold.fold, ih]
    unfold update
    rw [a.step_eq c i (F.values c i) (ModularHistoryPass.values_length F c i), BoundedFold.accumulator_packet]
    rfl

theorem bound_unary (F : Family) (a : Access F) : UnaryFn (ModularHistoryPass.bound F) :=
  ((((UnaryFn.const 2).mul (UnaryFn.length a.modulus.bits_mem_FP)).add (UnaryFn.const 2))).mul a.count

def run (F : Family) (a : Access F) (c : List Bool) : List Bool :=
  BoundedFold.fold (update F a) (fun _ => []) c (F.count c)

theorem run_eq (F : Family) (a : Access F) (c : List Bool) : run F a c = WordList.encode ((F.values c (F.count c)).map residueBits) := fold_encoded F a c _

theorem run_evaluator (F : Family) (a : Access F) : SpaceFunction (run F a) := by
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP (bound_unary F a).mem_FP
  have HB : ∀ c, ModularHistoryPass.bound F c ≤ p.eval c.length := by
    intro c
    simpa only [List.length_replicate] using hp c
  have E := BoundedFold.evaluator (update_evaluator F a) (fun c => BinaryNatCode.encode (F.count c)) (fun _ => [])
    (BinaryFn.ofUnary a.count).bits_mem_FP (constFn_mem_FP []) p (fun c i hi => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits] at hi
      rw [fold_encoded]
      exact (ModularHistoryPass.table_length F c i hi).trans (HB c))
  exact E.congr (funext fun c => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

def read (F : Family) (a : Access F) (index : List Bool → ℕ) (c : List Bool) : List Bool :=
  WordList.reader (pair (run F a c) (BinaryNatCode.encode (index c)))

theorem read_evaluator (F : Family) (a : Access F) (index : List Bool → ℕ) (hi : BinaryFn index) : SpaceFunction (read F a index) :=
  ((run_evaluator F a).pairOutputs (SpaceFunction.ofFP _ hi.bits_mem_FP)).postcompose WordList.reader WordList.reader_FP

theorem read_eq (F : Family) (a : Access F) (index : List Bool → ℕ) (c : List Bool) :
    read F a index c = (((F.values c (F.count c)).map residueBits)[index c]?).getD [] := by
  rw [read, WordList.reader_packet, run_eq, WordList.get_encode]
end LeanCanny.Algebra.ModularHistoryPassSpace
