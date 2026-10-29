/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineRow
public import LeanCanny.ETR.ComplexGradientFamily

/-! # Shared original affine critical stage circuits

Each stage differentiates only the original source program. Existing normal
and ancestral-level wires supply the affine rows; prior stage programs are
not copied into each derivative call.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.AffineStage
open MvPolynomial
open scoped Classical BigOperators

structure Inputs where
  base : ℕ
  start : ℕ
  ambient : ℕ
  multipliers : ℕ
  count : ℕ
  source : List Operation
  sourceOutput : ℕ
  normal : ℕ → ℕ → ℕ
  level : ℕ → ℕ
  active : ℕ → Bool

structure Inputs.Valid (C : Inputs) : Prop where
  source : StraightLine.WellFormed C.start C.source
  start : C.start ≤ C.base
  output : C.sourceOutput < C.start + C.source.length
  positive : 0 < C.count
  ambient : C.ambient + C.count ≤ C.base
  multipliers : C.multipliers + (C.count + 1) ≤ C.base
  normal : ∀ r < C.count + 1, ∀ i < C.count, C.normal r i < C.base
  level : ∀ r < C.count, C.level r < C.base

def copyBase (C : Inputs) : ℕ := C.base + 1
def gradientBase (C : Inputs) : ℕ := copyBase C + C.count * GradientFamily.stride C.start C.source
def gradientStart (C : Inputs) (i : ℕ) : ℕ := gradientBase C + i * AffineRow.stride (C.count + 1)
def heightBase (C : Inputs) : ℕ := gradientBase C + C.count * AffineRow.stride (C.count + 1)
def heightStart (C : Inputs) (r : ℕ) : ℕ := heightBase C + r * AffineRow.stride C.count

def derivative (C : Inputs) (i : ℕ) : ℕ :=
  GradientFamily.derivativeWire (copyBase C) C.start C.source i C.sourceOutput

def gradientRow (C : Inputs) (i : ℕ) : List Operation :=
  AffineRow.difference C.base (gradientStart C i) C.multipliers (C.count + 1) (derivative C i) (fun r => C.normal r i)
def heightRow (C : Inputs) (r : ℕ) : List Operation :=
  AffineRow.height C.base (heightStart C r) C.ambient C.count (C.level r) (C.normal (r + 1))

def gradientPrefix (C : Inputs) : ℕ → List Operation
  | 0 => []
  | k + 1 => gradientPrefix C k ++ gradientRow C k

def heightPrefix (C : Inputs) : ℕ → List Operation
  | 0 => []
  | k + 1 => heightPrefix C k ++ heightRow C k

def gradientGates (C : Inputs) (k : ℕ) : List Gate := StraightLine.gates (gradientBase C) (gradientPrefix C k)
def heightGates (C : Inputs) (k : ℕ) : List Gate := StraightLine.gates (heightBase C) (heightPrefix C k)

def program (C : Inputs) : List Operation := .constant 0 ::
  (GradientFamily.program C.base (copyBase C) C.start C.ambient C.source C.count ++
    (gradientPrefix C C.count ++ heightPrefix C C.count))

def gates (C : Inputs) : List Gate := StraightLine.gates C.base (program C)

def gradientOutput (C : Inputs) (i : ℕ) : ℕ := AffineRow.output (gradientStart C i) (C.count + 1)
def sourceOutput (C : Inputs) : ℕ := GradientFamily.valueWire (copyBase C) C.start C.source 0 C.sourceOutput
def heightOutput (C : Inputs) (r : ℕ) : ℕ :=
  if C.active r then AffineRow.output (heightStart C r) C.count else C.multipliers + (r + 1)

def output (C : Inputs) (j : ℕ) : ℕ :=
  if j < C.count then gradientOutput C j else
  if j = C.count then sourceOutput C else heightOutput C (j - (C.count + 1))

theorem gradientPrefix_length (C : Inputs) (k : ℕ) :
    (gradientPrefix C k).length = k * AffineRow.stride (C.count + 1) := by
  induction k with
  | zero => simp only [gradientPrefix, List.length_nil, Nat.zero_mul]
  | succ k ih => rw [gradientPrefix, List.length_append, gradientRow, AffineRow.difference_length, ih, Nat.succ_mul]

theorem heightPrefix_length (C : Inputs) (k : ℕ) :
    (heightPrefix C k).length = k * AffineRow.stride C.count := by
  induction k with
  | zero => simp only [heightPrefix, List.length_nil, Nat.zero_mul]
  | succ k ih => rw [heightPrefix, List.length_append, heightRow, AffineRow.height_length, ih, Nat.succ_mul]

theorem gradientGates_succ (C : Inputs) (k : ℕ) :
    gradientGates C (k + 1) = gradientGates C k ++ StraightLine.gates (gradientStart C k) (gradientRow C k) := by
  rw [gradientGates, gradientPrefix, StraightLine.gates_append, gradientPrefix_length]
  rfl

theorem heightGates_succ (C : Inputs) (k : ℕ) :
    heightGates C (k + 1) = heightGates C k ++ StraightLine.gates (heightStart C k) (heightRow C k) := by
  rw [heightGates, heightPrefix, StraightLine.gates_append, heightPrefix_length]
  rfl

theorem gradientGates_range (C : Inputs) (k : ℕ) :
    gradientGates C k = (List.range k).flatMap (fun i => StraightLine.gates (gradientStart C i) (gradientRow C i)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [gradientGates_succ, ih, List.range_succ, List.flatMap_append]; simp

theorem heightGates_range (C : Inputs) (k : ℕ) :
    heightGates C k = (List.range k).flatMap (fun r => StraightLine.gates (heightStart C r) (heightRow C r)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [heightGates_succ, ih, List.range_succ, List.flatMap_append]; simp

theorem program_length (C : Inputs) : (program C).length =
    1 + C.count * GradientFamily.stride C.start C.source +
      C.count * AffineRow.stride (C.count + 1) + C.count * AffineRow.stride C.count := by
  simp only [program, List.length_cons, List.length_append, GradientFamily.program_length,
    gradientPrefix_length, heightPrefix_length]
  omega

theorem gates_eq (C : Inputs) : gates C = .constant C.base 0 ::
    (GradientFamily.gates C.base (copyBase C) C.start C.ambient C.source C.count ++
      (gradientGates C C.count ++ heightGates C C.count)) := by
  rw [gates, program, StraightLine.gates, StraightLine.gates_append, GradientFamily.program_length,
    StraightLine.gates_append, gradientPrefix_length]
  rfl

theorem derivative_lt (C : Inputs) (h : C.Valid) (i : ℕ) (hi : i < C.count) : derivative C i < gradientBase C :=
  GradientFamily.derivativeWire_lt_end (copyBase C) C.start C.source C.count i C.sourceOutput hi h.output

theorem gradientPrefix_wellFormed (C : Inputs) (h : C.Valid) (k : ℕ) (hk : k ≤ C.count) :
    StraightLine.WellFormed (gradientBase C) (gradientPrefix C k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [gradientPrefix, StraightLine.wellFormed_append, gradientPrefix_length]
    refine ⟨ih (by omega), ?_⟩
    have hbase : C.base < gradientStart C k := by unfold gradientStart gradientBase copyBase; omega
    have hrow : gradientBase C ≤ gradientStart C k := by unfold gradientStart; omega
    apply AffineRow.difference_wellFormed _ _ _ _ _ _ hbase ?_ (h.multipliers.trans (by omega))
      ((derivative_lt C h k (by omega)).trans_le hrow)
    intro r hr
    exact (h.normal r hr k (by omega)).trans hbase

theorem heightPrefix_wellFormed (C : Inputs) (h : C.Valid) (k : ℕ) (hk : k ≤ C.count) :
    StraightLine.WellFormed (heightBase C) (heightPrefix C k) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    rw [heightPrefix, StraightLine.wellFormed_append, heightPrefix_length]
    refine ⟨ih (by omega), ?_⟩
    have hbase : C.base < heightStart C k := by unfold heightStart heightBase gradientBase copyBase; omega
    apply AffineRow.height_wellFormed _ _ _ _ _ _ hbase ?_ (h.ambient.trans (by omega))
      ((h.level k (by omega)).trans hbase)
    intro i hi
    exact (h.normal (k + 1) (by omega) i hi).trans hbase

theorem wellFormed (C : Inputs) (h : C.Valid) : StraightLine.WellFormed C.base (program C) := by
  refine ⟨trivial, ?_⟩
  rw [StraightLine.wellFormed_append, GradientFamily.program_length]
  refine ⟨GradientFamily.wellFormed C.base (copyBase C) C.start C.ambient C.source C.count
    (by unfold copyBase; omega) (h.start.trans (by unfold copyBase; omega)) h.source, ?_⟩
  rw [StraightLine.wellFormed_append, gradientPrefix_length]
  exact ⟨gradientPrefix_wellFormed C h _ le_rfl, heightPrefix_wellFormed C h _ le_rfl⟩

theorem output_lt (C : Inputs) (h : C.Valid) (j : ℕ) (hj : j < C.count + (C.count + 1)) :
    output C j < C.base + (program C).length := by
  have hend : C.base + (program C).length = heightBase C + C.count * AffineRow.stride C.count := by
    rw [program_length]
    unfold heightBase gradientBase copyBase
    omega
  rw [hend]
  unfold output
  split_ifs with hi he
  · exact (AffineRow.output_lt_end (gradientBase C) (C.count + 1) C.count j hi).trans_le (Nat.le_add_right _ _)
  · exact (GradientFamily.valueWire_lt_end (copyBase C) C.start C.source C.count 0 C.sourceOutput h.positive h.output).trans_le
      (by unfold heightBase gradientBase; omega)
  · have hr : j - (C.count + 1) < C.count := by omega
    unfold heightOutput
    split_ifs
    · exact AffineRow.output_lt_end _ _ _ _ hr
    · have H := h.multipliers
      have hb : C.base < heightBase C := by unfold heightBase gradientBase copyBase; omega
      omega

end LeanCanny.ETR.ComplexCircuit.AffineStage
