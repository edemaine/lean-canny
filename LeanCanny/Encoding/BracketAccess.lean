/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BracketsFP

/-!
# Polynomial-time access to encoded tree nodes

Searching for the first positive prefix with equally many opening and closing
brackets splits off the first complete node. The splitter is total on arbitrary
strings, and its exact behavior is proved on a serialized node followed by any suffix.
-/

@[expose] public section

namespace LeanCanny.Encoding.Brackets

/-- Position of the first closing bracket that returns to depth zero, or the input
length if there is no such prefix. This is a bounded search on the literal input. -/
def firstReturn (bits : List Bool) : ℕ :=
  (List.range bits.length).findIdx fun i =>
    decide ((bits.take (i + 1)).count false = (bits.take (i + 1)).count true)

theorem firstReturn_unary : UnaryFn firstReturn := by
  have hp : FPPred fun w : List Bool =>
      ((pairFst w).take ((pairSnd w).length + 1)).count false =
        ((pairFst w).take ((pairSnd w).length + 1)).count true :=
    FPPred.eq
      (prefixFalse_unary pairFst_mem_FP (UnaryFn.index.add (UnaryFn.const 1)))
      (prefixTrue_unary pairFst_mem_FP (UnaryFn.index.add (UnaryFn.const 1)))
  exact ((UnaryFn.length id_mem_FP).find hp).of_eq fun bits => by
    simp only [firstReturn, pairFst_pair, pairSnd_pair, List.length_replicate, id_eq]

theorem firstReturn_toBits_append (d : Data) (suffix : List Bool) :
    firstReturn (d.toBits ++ suffix) = d.toBits.length - 1 := by
  have hpos : 0 < d.toBits.length := by simp
  have hd := treeCode_toBits d
  have hidx : d.toBits.length - 1 < (List.range (d.toBits ++ suffix).length).length := by
    simp only [List.length_range, List.length_append]
    omega
  rw [firstReturn, List.findIdx_eq hidx]
  simp_rw [List.getElem_range, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rw [Nat.sub_add_cancel hpos, List.take_left]
    exact hd.1.1
  · intro j hj
    have hjd : j + 1 < d.toBits.length := by omega
    rw [List.take_append_of_le_length hjd.le]
    exact (hd.2.2 (j + 1) hjd (by omega)).ne'

/-- Length consumed by a total splitter; a failed search consumes the whole string. -/
def nodeLength (bits : List Bool) : ℕ := min bits.length (firstReturn bits + 1)

def firstNode (bits : List Bool) : List Bool := bits.take (nodeLength bits)

def afterNode (bits : List Bool) : List Bool := bits.drop (nodeLength bits)

theorem nodeLength_unary : UnaryFn nodeLength :=
  (UnaryFn.length id_mem_FP).min (firstReturn_unary.add (UnaryFn.const 1))

theorem firstNode_mem_FP : firstNode ∈ FP := take_mem_FP id_mem_FP nodeLength_unary

theorem afterNode_mem_FP : afterNode ∈ FP := drop_mem_FP id_mem_FP nodeLength_unary

theorem nodeLength_toBits_append (d : Data) (suffix : List Bool) :
    nodeLength (d.toBits ++ suffix) = d.toBits.length := by
  have hpos : 0 < d.toBits.length := by simp
  simp only [nodeLength, firstReturn_toBits_append, List.length_append]
  omega

@[simp] theorem firstNode_toBits_append (d : Data) (suffix : List Bool) :
    firstNode (d.toBits ++ suffix) = d.toBits := by
  rw [firstNode, nodeLength_toBits_append, List.take_left]

@[simp] theorem afterNode_toBits_append (d : Data) (suffix : List Bool) :
    afterNode (d.toBits ++ suffix) = suffix := by
  rw [afterNode, nodeLength_toBits_append, List.drop_left]

/-- Add one enclosing bracket pair around a serialized forest. -/
def wrap (bits : List Bool) : List Bool := false :: (bits ++ [true])

theorem wrap_mem_FP : wrap ∈ FP :=
  mem_FP_comp (appendFn_mem_FP id_mem_FP (constFn_mem_FP [true]))
    (cons_mem_FP false)

/-- Strip the enclosing bracket pair. This operation is total on malformed inputs. -/
def contents (bits : List Bool) : List Bool := (bits.drop 1).take (bits.length - 2)

theorem contents_mem_FP : contents ∈ FP :=
  take_mem_FP (drop_mem_FP id_mem_FP (UnaryFn.const 1))
    ((UnaryFn.length id_mem_FP).sub (UnaryFn.const 2))

@[simp] theorem contents_toBits (xs : List Data) :
    contents (Data.l xs).toBits = (xs.map Data.toBits).flatten := by
  rw [contents, Data.toBits_l]
  simp

/-- Encoded cons, taking a node and an encoded list node. -/
def consNode (head tail : List Bool) : List Bool := false :: (head ++ tail.drop 1)

theorem consNode_mem_FP {head tail : List Bool → List Bool}
    (hhead : head ∈ FP) (htail : tail ∈ FP) :
    (fun z => consNode (head z) (tail z)) ∈ FP :=
  mem_FP_comp (appendFn_mem_FP hhead (drop_mem_FP htail (UnaryFn.const 1)))
    (cons_mem_FP false)

@[simp] theorem consNode_toBits (d : Data) (xs : List Data) :
    consNode d.toBits (Data.l xs).toBits = (Data.l (d :: xs)).toBits := by
  simp [consNode, Data.toBits_l]

def firstChild (bits : List Bool) : List Bool := firstNode (contents bits)

def remainingChildren (bits : List Bool) : List Bool := wrap (afterNode (contents bits))

theorem firstChild_mem_FP : firstChild ∈ FP := mem_FP_comp contents_mem_FP firstNode_mem_FP

theorem remainingChildren_mem_FP : remainingChildren ∈ FP :=
  mem_FP_comp (mem_FP_comp contents_mem_FP afterNode_mem_FP) wrap_mem_FP

@[simp] theorem firstChild_toBits (d : Data) (xs : List Data) :
    firstChild (Data.l (d :: xs)).toBits = d.toBits := by
  simp only [firstChild, contents_toBits, List.map_cons, List.flatten_cons, firstNode_toBits_append]

@[simp] theorem remainingChildren_toBits (d : Data) (xs : List Data) :
    remainingChildren (Data.l (d :: xs)).toBits = (Data.l xs).toBits := by
  unfold remainingChildren
  rw [contents_toBits]
  simp only [List.map_cons, List.flatten_cons, afterNode_toBits_append]
  rw [wrap, Data.toBits_l]

end LeanCanny.Encoding.Brackets
