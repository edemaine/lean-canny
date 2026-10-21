/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.Data
public import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Recognizing serialized rose trees by bracket counts

`false` opens a node and `true` closes it. A single serialized `Data` tree is a
nonempty balanced word whose proper nonempty prefixes have strictly more opens
than closes. Mathlib's Dyck-word/tree equivalence supplies the converse, so this
criterion recognizes precisely the image of the actual dependency codec.
-/

@[expose] public section

namespace LeanCanny.Encoding.Brackets

def step (b : Bool) : DyckStep := if b then .D else .U

def bit : DyckStep → Bool
  | .U => false
  | .D => true

@[simp] theorem bit_step (b : Bool) : bit (step b) = b := by cases b <;> rfl

@[simp] theorem step_bit (s : DyckStep) : step (bit s) = s := by cases s <;> rfl

@[simp] theorem count_U_map (bits : List Bool) :
    (bits.map step).count .U = bits.count false := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [step, ih]

@[simp] theorem count_D_map (bits : List Bool) :
    (bits.map step).count .D = bits.count true := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [step, ih]

@[simp] theorem count_false_map (ss : List DyckStep) :
    (ss.map bit).count false = ss.count .U := by
  induction ss with
  | nil => rfl
  | cons s ss ih => cases s <;> simp [bit, ih]

@[simp] theorem count_true_map (ss : List DyckStep) :
    (ss.map bit).count true = ss.count .D := by
  induction ss with
  | nil => rfl
  | cons s ss ih => cases s <;> simp [bit, ih]

def Balanced (bits : List Bool) : Prop :=
  bits.count false = bits.count true ∧
    ∀ i ≤ bits.length, (bits.take i).count true ≤ (bits.take i).count false

def TreeCode (bits : List Bool) : Prop :=
  Balanced bits ∧ bits ≠ [] ∧
    ∀ i < bits.length, 0 < i → (bits.take i).count true < (bits.take i).count false

/-- Turn the bounded prefix-count criterion into Mathlib's Dyck-word structure. -/
def toDyck (bits : List Bool) (h : Balanced bits) : DyckWord where
  toList := bits.map step
  count_U_eq_count_D := by simpa using h.1
  count_D_le_count_U i := by
    simp only [← List.map_take, count_D_map, count_U_map]
    by_cases hi : i ≤ bits.length
    · exact h.2 i hi
    · rw [List.take_of_length_le (by omega)]
      exact h.1.ge

def ofDyck (p : DyckWord) : List Bool := p.toList.map bit

@[simp] theorem ofDyck_toDyck (bits : List Bool) (h : Balanced bits) :
    ofDyck (toDyck bits h) = bits := by
  simp [ofDyck, toDyck, List.map_map, Function.comp_def]

@[simp] theorem ofDyck_zero : ofDyck 0 = [] := rfl

@[simp] theorem ofDyck_add (p q : DyckWord) : ofDyck (p + q) = ofDyck p ++ ofDyck q := by
  change (p.toList ++ q.toList).map bit = _
  exact List.map_append

@[simp] theorem ofDyck_nest (p : DyckWord) :
    ofDyck p.nest = false :: (ofDyck p ++ [true]) := by
  simp [ofDyck, DyckWord.nest, bit]

@[simp] theorem ofDyck_sum (ps : List DyckWord) :
    ofDyck ps.sum = (ps.map ofDyck).flatten := by
  induction ps <;> simp_all

theorem balanced_ofDyck (p : DyckWord) : Balanced (ofDyck p) := by
  constructor
  · simpa only [ofDyck, count_false_map, count_true_map] using p.count_U_eq_count_D
  · intro i _
    simpa only [ofDyck, ← List.map_take, count_true_map, count_false_map] using
      p.count_D_le_count_U i

theorem treeCode_of_nested (p : DyckWord) (h : p.IsNested) : TreeCode (ofDyck p) := by
  refine ⟨balanced_ofDyck p, ?_, ?_⟩
  · simpa [ofDyck] using DyckWord.toList_ne_nil.mpr h.1
  · intro i hi hpos
    have hn := h.2 hpos (by simpa only [ofDyck, List.length_map] using hi)
    simpa only [ofDyck, ← List.map_take, count_true_map, count_false_map] using hn

theorem nested_toDyck (bits : List Bool) (h : TreeCode bits) : (toDyck bits h.1).IsNested := by
  constructor
  · intro hz
    have he := congrArg ofDyck hz
    simp only [ofDyck_toDyck, ofDyck_zero] at he
    exact h.2.1 he
  · intro i hpos hi
    have hn := h.2.2 i (by simpa only [toDyck, List.length_map] using hi) hpos
    simpa only [toDyck, ← List.map_take, count_U_map, count_D_map] using hn

/-- The Dyck word for a `Data` node nests the concatenation of its children's words. -/
def dataDyck : Data → DyckWord
  | .l xs => (xs.map dataDyck).sum.nest

theorem ofDyck_dataDyck (d : Data) : ofDyck (dataDyck d) = d.toBits := by
  induction d using Data.inductionL with
  | nil => simp [dataDyck, Data.toBits_l]
  | cons d ds ihd ihds =>
      have hinside : ofDyck (ds.map dataDyck).sum = (ds.map Data.toBits).flatten := by
        simp only [dataDyck, ofDyck_nest, Data.toBits_l] at ihds
        exact List.append_cancel_right (List.cons.inj ihds).2
      simp only [dataDyck, List.map_cons, List.sum_cons, ofDyck_nest, ofDyck_add,
        ihd, hinside, Data.toBits_l, List.flatten_cons]

theorem treeCode_toBits (d : Data) : TreeCode d.toBits := by
  cases d with
  | l ds =>
      rw [← ofDyck_dataDyck]
      rw [dataDyck]
      exact treeCode_of_nested _ DyckWord.IsNested.nest

/-- The usual left-child/right-sibling interpretation of a binary tree as a rose forest. -/
def forest : BinaryTree Unit → List Data
  | .nil => []
  | .node _ l r => .l (forest l) :: forest r

theorem forest_bits (t : BinaryTree Unit) :
    ((forest t).map Data.toBits).flatten = ofDyck (DyckWord.ofTree t) := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      simp [forest, DyckWord.ofTree, Data.toBits_l, ihl, ihr]

theorem exists_forest (p : DyckWord) :
    ∃ xs : List Data, ofDyck p = (xs.map Data.toBits).flatten := by
  exact ⟨forest p.toTree, by rw [forest_bits, DyckWord.ofTree_toTree]⟩

/-- The numerical bracket criterion recognizes exactly a complete single serialized tree. -/
theorem treeCode_iff (bits : List Bool) : TreeCode bits ↔ ∃ d : Data, bits = d.toBits := by
  constructor
  · intro h
    let p := toDyck bits h.1
    have hn : p.IsNested := nested_toDyck bits h
    obtain ⟨xs, hx⟩ := exists_forest (p.denest hn)
    refine ⟨.l xs, ?_⟩
    calc
      bits = ofDyck p := (ofDyck_toDyck bits h.1).symm
      _ = ofDyck (p.denest hn).nest := congrArg ofDyck (p.nest_denest hn).symm
      _ = (Data.l xs).toBits := by rw [ofDyck_nest, hx, Data.toBits_l]
  · rintro ⟨d, rfl⟩
    exact treeCode_toBits d

/-- The dependency's parser succeeds on every string accepted by the numerical test. -/
theorem fromBits_of_treeCode {bits : List Bool} (h : TreeCode bits) :
    ∃ d : Data, Data.fromBits bits = some d ∧ bits = d.toBits := by
  obtain ⟨d, rfl⟩ := (treeCode_iff bits).mp h
  exact ⟨d, Data.fromBits_toBits d, rfl⟩

end LeanCanny.Encoding.Brackets
