/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularFoldFP
public import LeanCanny.Encoding.WordListFP

/-! # Polynomial-time modular passes over bounded retained histories

Each step reads a table of earlier canonical residues and prepends one new
residue. The count is unary and each word fits in the caller modulus, so
both the complete table and lookup in that table have native FP programs.
No algebraic coefficient reader is assumed by this compiler.
-/

@[expose] public section
namespace LeanCanny.Algebra.ModularHistoryPass
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

structure Family where
  count : List Bool → ℕ
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0
  next : (c : List Bool) → ℕ → List (ZMod (modulus c)) → ZMod (modulus c)

def Family.values (F : Family) (c : List Bool) : ℕ → List (ZMod (F.modulus c))
  | 0 => []
  | i + 1 => F.next c i (F.values c i) :: F.values c i

theorem values_length (F : Family) (c : List Bool) (i : ℕ) : (F.values c i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Family.values, List.length_cons, ih]

structure Access (F : Family) where
  count : UnaryFn F.count
  modulus : BinaryFn F.modulus
  step : List Bool → List Bool
  step_FP : step ∈ FP
  step_eq : ∀ c i (v : List (ZMod (F.modulus c))), v.length = i →
    step (BoundedFold.packet c i (WordList.encode (v.map residueBits))) = residueBits (F.next c i v)

def update (F : Family) (a : Access F) (p : List Bool) : List Bool :=
  pair (a.step p) (BoundedFold.accumulator p)

theorem update_FP (F : Family) (a : Access F) : update F a ∈ FP :=
  mem_FP_pair a.step_FP BoundedFold.accumulator_mem_FP

theorem fold_encoded (F : Family) (a : Access F) (c : List Bool) (i : ℕ) :
    BoundedFold.fold (update F a) (fun _ => []) c i = WordList.encode ((F.values c i).map residueBits) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [BoundedFold.fold, ih]
    unfold update
    rw [a.step_eq c i (F.values c i) (values_length F c i), BoundedFold.accumulator_packet]
    rfl

theorem residue_length (F : Family) (c : List Bool) (x : ZMod (F.modulus c)) :
    (residueBits x).length ≤ (BinaryNatCode.encode (F.modulus c)).length := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  apply ModularFold.bits_length_le (fun c => BinaryNatCode.encode (F.modulus c)) c x.val
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt x

def bound (F : Family) (c : List Bool) : ℕ :=
  (2 * (BinaryNatCode.encode (F.modulus c)).length + 2) * F.count c

theorem bound_unary (F : Family) (a : Access F) : UnaryFn (bound F) :=
  ((((UnaryFn.const 2).mul (UnaryFn.length a.modulus.bits_mem_FP)).add (UnaryFn.const 2))).mul a.count

theorem table_length (F : Family) (c : List Bool) (i : ℕ) (hi : i ≤ F.count c) :
    (WordList.encode ((F.values c i).map residueBits)).length ≤ bound F c := by
  have H := WordList.length_le ((F.values c i).map residueBits) (BinaryNatCode.encode (F.modulus c)).length (by
    intro w hw
    obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hw
    exact residue_length F c x)
  rw [List.length_map, values_length] at H
  exact H.trans (Nat.mul_le_mul_left _ hi)

def run (F : Family) (a : Access F) (c : List Bool) : List Bool :=
  BoundedFold.fold (update F a) (fun _ => []) c (F.count c)

theorem run_FP (F : Family) (a : Access F) : run F a ∈ FP :=
  BoundedFold.evaluator_FP (update F a) (fun _ => []) F.count (bound F) (update_FP F a) (constFn_mem_FP [])
    a.count (bound_unary F a) (fun c i hi => by rw [fold_encoded]; exact table_length F c i hi)

theorem run_eq (F : Family) (a : Access F) (c : List Bool) :
    run F a c = WordList.encode ((F.values c (F.count c)).map residueBits) := fold_encoded F a c _

def read (F : Family) (a : Access F) (index : List Bool → ℕ) (c : List Bool) : List Bool :=
  WordList.reader (pair (run F a c) (BinaryNatCode.encode (index c)))

theorem read_FP (F : Family) (a : Access F) (index : List Bool → ℕ) (hi : BinaryFn index) : read F a index ∈ FP :=
  mem_FP_comp (mem_FP_pair (run_FP F a) hi.bits_mem_FP) WordList.reader_FP

theorem read_eq (F : Family) (a : Access F) (index : List Bool → ℕ) (c : List Bool) :
    read F a index c = (((F.values c (F.count c)).map residueBits)[index c]?).getD [] := by
  rw [read, WordList.reader_packet, run_eq, WordList.get_encode]

end LeanCanny.Algebra.ModularHistoryPass
