/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateHeightRecord
public import LeanCanny.Encoding.FlatAffineFrozenLevelRecord

/-! # Native fixed-height and midpoint child records

A height child retains one critical block; a midpoint child retains two.
The current objective advances by one coordinate. Earlier stages are kept,
and copied levels freeze their original references before ancestry grows.
All readers are constructed from the original source controls.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (stage levelQuery)
set_option backward.isDefEq.respectTransparency false

def copies (midpoint : Bool) : ℕ := if midpoint then 2 else 1

def childDepth (midpoint : Bool) (depth : List Bool → ℕ) (u : List Bool) : ℕ :=
  depth u + copies midpoint

def originalStage (depth : List Bool → ℕ) (q : List Bool) : List Bool :=
  stage (pairFst q) (depth (pairFst q))

theorem originalStage_FP {depth : List Bool → ℕ} (hd : UnaryFn depth) : originalStage depth ∈ FP :=
  mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary (hd.comp pairFst_mem_FP)).bits_mem_FP

def objective (midpoint : Bool) (depth old : List Bool → ℕ) (q : List Bool) : ℕ :=
  if Nat.fromBitsLE (pairSnd q) < depth (pairFst q) then old q else
    old (originalStage depth q) +
      if Nat.fromBitsLE (pairSnd q) = childDepth midpoint depth (pairFst q) then 1 else 0

theorem objective_unary (midpoint : Bool) {depth old : List Bool → ℕ}
    (hd : UnaryFn depth) (ho : UnaryFn old) : UnaryFn (objective midpoint depth old) := by
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hbefore := hi.lt (BinaryFn.ofUnary (hd.comp pairFst_mem_FP))
  have hlast := hi.eq (BinaryFn.ofUnary ((hd.add (UnaryFn.const (copies midpoint))).comp pairFst_mem_FP))
  have hinc : UnaryFn (fun q => if Nat.fromBitsLE (pairSnd q) = childDepth midpoint depth (pairFst q) then 1 else 0) :=
    hlast.computable.ite_decide (UnaryFn.const 1) (UnaryFn.const 0)
  exact hbefore.computable.ite_decide ho ((ho.comp (originalStage_FP hd)).add hinc)

def coordinate (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool) : ℕ :=
  min (old (stage u (depth u))) (P.dim u + 3)

theorem coordinate_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) : UnaryFn (coordinate P depth old) :=
  (ho.comp (mem_FP_pair id_mem_FP (BinaryFn.ofUnary hd).bits_mem_FP)).min (hP.dim.add (UnaryFn.const 3))

def originalQuery (depth : List Bool → ℕ) (q : List Bool) : List Bool :=
  pair (originalStage depth (pairFst q)) (pairSnd q)

theorem originalQuery_FP {depth : List Bool → ℕ} (hd : UnaryFn depth) : originalQuery depth ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (originalStage_FP hd)) pairSnd_mem_FP

def newLevel (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) : List Bool :=
  if midpoint then
    CoordinateHeightRecord.midpoint (P.dim u + 4) (coordinate P depth old u) (depth u) (depth u + 1)
  else CoordinateHeightRecord.height (P.dim u + 4) (coordinate P depth old u) (depth u)

theorem newLevel_FP (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) : newLevel midpoint P depth old ∈ FP := by
  cases midpoint with
  | false =>
    exact CoordinateHeightRecord.height_FP (hP.dim.add (UnaryFn.const 4))
      (BinaryFn.ofUnary (coordinate_unary hP hd ho)) (BinaryFn.ofUnary hd)
  | true =>
    exact CoordinateHeightRecord.midpoint_FP (hP.dim.add (UnaryFn.const 4))
      (BinaryFn.ofUnary (coordinate_unary hP hd ho)) (BinaryFn.ofUnary hd)
      (BinaryFn.ofUnary (hd.add (UnaryFn.const 1)))

def isNewLevel (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (q : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd (pairFst q)) = childDepth midpoint depth (pairFst (pairFst q))) &&
    decide (Nat.fromBitsLE (pairSnd q) = coordinate P depth old (pairFst (pairFst q)))

theorem isNewLevel_FP (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) :
    (fun q => [isNewLevel midpoint P depth old q]) ∈ FP := by
  have hs : (fun q => pairFst (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have ht : BinaryFn (fun q => Nat.fromBitsLE (pairSnd (pairFst q))) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp pairFst_mem_FP
  have hl := ht.eq (BinaryFn.ofUnary ((hd.add (UnaryFn.const (copies midpoint))).comp hs))
  have hi := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.ofUnary ((coordinate_unary hP hd ho).comp hs))
  exact (hl.and hi).flag_mem_FP

def levels (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd (pairFst q)) < depth (pairFst (pairFst q)) then level q else
    if isNewLevel midpoint P depth old q then newLevel midpoint P depth old (pairFst (pairFst q)) else
      FlatAffineFrozenLevelRecord.freeze (depth (pairFst (pairFst q))) (level (originalQuery depth q))

theorem levels_evaluator (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level) :
    SpaceFunction (levels midpoint P depth old level) := by
  have hs : (fun q => pairFst (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hf := FlatAffineFrozenLevelRecord.reader_evaluator (hd.comp hs) (hl.precompose _ (originalQuery_FP hd))
  have hn := SpaceFunction.ofFP _ (mem_FP_comp hs (newLevel_FP midpoint hP hd ho))
  have hb := SpaceFunction.branch _ (isNewLevel_FP midpoint hP hd ho) hn hf
  have hi : BinaryFn (fun q => Nat.fromBitsLE (pairSnd (pairFst q))) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp pairFst_mem_FP
  have ht := hi.lt (BinaryFn.ofUnary (hd.comp hs))
  exact (SpaceFunction.branch _ ht.flag_mem_FP hl hb).congr (funext fun q => by
    simp only [levels, decide_eq_true_eq, Function.comp_apply, FlatAffineFrozenLevelRecord.reader])

theorem isNewLevel_at (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (u : List Bool) (k j : ℕ) :
    isNewLevel midpoint P depth old (levelQuery u k j) =
      (decide (k = childDepth midpoint depth u) && decide (j = coordinate P depth old u)) := by
  simp only [isNewLevel, levelQuery, stage, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem levels_before (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k j : ℕ) (hk : k < depth u) :
    levels midpoint P depth old level (levelQuery u k j) = level (levelQuery u k j) := by
  simp only [levels, levelQuery, stage, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, hk, ↓reduceIte]

theorem levels_copy (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k j : ℕ) (hk : depth u ≤ k)
    (hj : k ≠ childDepth midpoint depth u ∨ j ≠ coordinate P depth old u) :
    levels midpoint P depth old level (levelQuery u k j) =
      FlatAffineFrozenLevelRecord.freeze (depth u) (level (levelQuery u (depth u) j)) := by
  have hn : isNewLevel midpoint P depth old (levelQuery u k j) = false := by
    rw [isNewLevel_at]
    rcases hj with h | h <;> simp [h]
  unfold levels
  rw [hn]
  simp only [Bool.false_eq_true, ↓reduceIte, levelQuery, stage,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [ite_eq_right (by omega)]
  simp only [originalQuery, originalStage, stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode]

theorem levels_newest (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) :
    levels midpoint P depth old level
        (levelQuery u (childDepth midpoint depth u) (coordinate P depth old u)) =
      newLevel midpoint P depth old u := by
  have hc : 0 < copies midpoint := by cases midpoint <;> decide
  have hn : isNewLevel midpoint P depth old
      (levelQuery u (childDepth midpoint depth u) (coordinate P depth old u)) = true := by
    rw [isNewLevel_at]
    simp only [decide_true, Bool.and_self]
  unfold levels
  rw [hn]
  simp only [↓reduceIte, levelQuery, stage,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [ite_eq_right (by unfold childDepth; omega)]

def inputs (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffineFullSourceTower.Inputs :=
  CoordinateDoubleAffinePrefix.inputs P (childDepth midpoint depth) (objective midpoint depth old)
    (levels midpoint P depth old level)

theorem access (midpoint : Bool) {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    (inputs midpoint P depth old level).Access :=
  CoordinateDoubleAffinePrefix.access hP (hd.add (UnaryFn.const (copies midpoint)))
    (objective_unary midpoint hd ho) (levels_evaluator midpoint hP hd ho hl) hA

theorem cone (midpoint : Bool) (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) : FlatAffinePowerPositive.ConeCertificate (inputs midpoint P depth old level) :=
  CoordinateDoubleAffinePrefix.coneCertificate P (childDepth midpoint depth) (objective midpoint depth old)
    (levels midpoint P depth old level)

theorem objective_before (midpoint : Bool) (depth old : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (hk : k < depth u) : objective midpoint depth old (stage u k) = old (stage u k) := by
  simp only [objective, stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hk, ↓reduceIte]

theorem objective_retained (midpoint : Bool) (depth old : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (hk : depth u ≤ k) (hl : k < childDepth midpoint depth u) :
    objective midpoint depth old (stage u k) = old (stage u (depth u)) := by
  simp only [objective, originalStage, stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_zero]

theorem objective_newest (midpoint : Bool) (depth old : List Bool → ℕ) (u : List Bool) :
    objective midpoint depth old (stage u (childDepth midpoint depth u)) = old (stage u (depth u)) + 1 := by
  have hc : 0 < copies midpoint := by cases midpoint <;> decide
  simp only [objective, originalStage, stage, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [ite_eq_right (by unfold childDepth; omega), ite_true]

end LeanCanny.Encoding.CoordinateDoubleAffineChildRecords
