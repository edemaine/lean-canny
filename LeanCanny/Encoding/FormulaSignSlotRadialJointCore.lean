/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialJointTermCopy
/-! # One actual integer equation for both closed lifts and a radial anchor

This core enforces literal polynomial equations, shared center and anchor
coordinates, and 0<parameter<bound. Component and cut-free conditions remain
separate predicates; the core alone does not assert their sampling existence.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointCore
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open FormulaSignSlotRadialJointLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def circle (side : Bool) (q : List Bool) :=
  FormulaSignSlotRadialJointTermCopy.copy false side (CanonicalAuxiliaryCandidateCover.equation (source side q))
noncomputable def radial (q : List Bool) := FormulaSignSlotRadialJointTermCopy.copy true false
  (FormulaSignSlotRadialFormalInput.equation (source true q))
noncomputable def oldCount (q : List Bool) := FormulaSignSlotMargin.initialDimension (source true q)
noncomputable def centerRow (q : List Bool) (i : ℕ) :=
  FormulaSignSlotRadialFormalInput.difference (centerVariable q i) (column 0 i)
def anchorRow (_q : List Bool) (i : ℕ) := FormulaSignSlotRadialFormalInput.difference (column 2 i) (column 1 i)
def sumRows (count : ℕ) (rows : ℕ → Term) := SumSquares.accumulate ((List.range count).map rows) (.const 0)
noncomputable def centerSquares (q : List Bool) := sumRows (centerCount q) (centerRow q)
noncomputable def anchorSquares (q : List Bool) := sumRows (oldCount q) (anchorRow q)
def positiveRow (term : Term) (witness : ℕ) : Term := .add (.mul term (Term.var witness).square) (.const (-1))
noncomputable def radiusRow (q : List Bool) := positiveRow (.var (radiusVariable q)) radiusWitness
noncomputable def gapRow (q : List Bool) := positiveRow
  (FormulaSignSlotRadialFormalInput.difference boundVariable (radiusVariable q)) gapWitness
noncomputable def equation (q : List Bool) : Term := .add (.add (circle false q).square (circle true q).square)
  (.add (radial q).square (.add (centerSquares q) (.add (anchorSquares q)
    (.add (radiusRow q).square (gapRow q).square))))

theorem circle_FP (side : Bool) : (fun q => (circle side q).toData.toBits) ∈ FP :=
  FormulaSignSlotRadialJointTermCopy.copy_FP false side
    (mem_FP_comp (source_FP side) CanonicalAuxiliaryCandidateCover.equation_FP)
theorem radial_FP : (fun q => (radial q).toData.toBits) ∈ FP :=
  FormulaSignSlotRadialJointTermCopy.copy_FP true false
    (mem_FP_comp (source_FP true) FormulaSignSlotRadialFormalInput.equation_FP)
theorem oldCount_unary : UnaryFn oldCount := FormulaSignSlotMargin.initialDimension_unary.comp (source_FP true)

private theorem difference_FP {left right : List Bool → ℕ} (hL : UnaryFn left) (hR : UnaryFn right) :
    (fun q => (FormulaSignSlotRadialFormalInput.difference (left q) (right q)).toData.toBits) ∈ FP := by
  have HL := Term.variableBits_mem_FP hL
  have HR := Term.variableBits_mem_FP hR
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HL
    (Codec.taggedTwo_mem_FP 3 (constFn_mem_FP (Term.const (-1)).toData.toBits) HR))
  intro q
  simp only [FormulaSignSlotRadialFormalInput.difference, Term.add_toBits, Term.mul_toBits, Term.variableBits_eq]

theorem centerRow_FP : (fun q => (centerRow (pairFst q) (pairSnd q).length).toData.toBits) ∈ FP :=
  difference_FP (((UnaryFn.const 4).mul ((spatialCount_unary.comp pairFst_mem_FP).add UnaryFn.index)).add (UnaryFn.const 2))
    ((UnaryFn.const 4).mul UnaryFn.index)
theorem anchorRow_FP : (fun q => (anchorRow (pairFst q) (pairSnd q).length).toData.toBits) ∈ FP :=
  difference_FP (((UnaryFn.const 4).mul UnaryFn.index).add (UnaryFn.const 2))
    (((UnaryFn.const 4).mul UnaryFn.index).add (UnaryFn.const 1))

private theorem sumRows_FP {count : List Bool → ℕ} {rows : List Bool → ℕ → Term}
    (hN : UnaryFn count) (hF : (fun q => (rows (pairFst q) (pairSnd q).length).toData.toBits) ∈ FP) :
    (fun q => (sumRows (count q) (rows q)).toData.toBits) ∈ FP := by
  have HF := flatMap_range_mem_FP hF hN.mem_FP
  have HB : (fun q => SumSquares.listBits ((List.range (count q)).map (rows q))) ∈ FP := by
    apply mem_FP_of_eq (mem_FP_comp HF Brackets.wrap_mem_FP)
    intro q
    simp only [Function.comp_apply, SumSquares.listBits, Data.toBits_l, List.map_map,
      List.flatten_eq_flatMap, List.flatMap_map, Function.comp_def, id_eq, Brackets.wrap,
      pairFst_pair, pairSnd_pair, List.length_replicate]
  apply mem_FP_of_eq (mem_FP_comp HB SumSquares.collapse_mem_FP)
  intro q
  rw [Function.comp_apply, SumSquares.collapse_listBits]
  rfl

theorem centerSquares_FP : (fun q => (centerSquares q).toData.toBits) ∈ FP := sumRows_FP centerCount_unary centerRow_FP
theorem anchorSquares_FP : (fun q => (anchorSquares q).toData.toBits) ∈ FP := sumRows_FP oldCount_unary anchorRow_FP

private theorem positiveRow_FP {t : List Bool → Term} (ht : (fun q => (t q).toData.toBits) ∈ FP) (witness : ℕ) :
    (fun q => (positiveRow (t q) witness).toData.toBits) ∈ FP := by
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 ht
    (constFn_mem_FP (Term.var witness).square.toData.toBits)) (constFn_mem_FP (Term.const (-1)).toData.toBits))
  intro q
  simp only [positiveRow, Term.add_toBits, Term.mul_toBits]

theorem radiusVariable_unary : UnaryFn radiusVariable :=
  ((UnaryFn.const 4).mul (spatialCount_unary.add centerCount_unary)).add (UnaryFn.const 2)
theorem radiusRow_FP : (fun q => (radiusRow q).toData.toBits) ∈ FP :=
  positiveRow_FP (mem_FP_of_eq (Term.variableBits_mem_FP radiusVariable_unary) (fun _ => Term.variableBits_eq _)) radiusWitness
theorem gapRow_FP : (fun q => (gapRow q).toData.toBits) ∈ FP :=
  positiveRow_FP (difference_FP (UnaryFn.const boundVariable) radiusVariable_unary) gapWitness

theorem equation_FP : (fun q => (equation q).toData.toBits) ∈ FP := by
  have square {t : List Bool → Term} (h : (fun q => (t q).toData.toBits) ∈ FP) :
      (fun q => (t q).square.toData.toBits) ∈ FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 h h) (fun _ => by rw [Term.square, Term.mul_toBits])
  have add {a b : List Bool → Term} (hA : (fun q => (a q).toData.toBits) ∈ FP)
      (hB : (fun q => (b q).toData.toBits) ∈ FP) : (fun q => (Term.add (a q) (b q)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 hA hB) (fun _ => (Term.add_toBits _ _).symm)
  exact add (add (square (circle_FP false)) (square (circle_FP true)))
    (add (square radial_FP) (add centerSquares_FP (add anchorSquares_FP
      (add (square radiusRow_FP) (square gapRow_FP)))))

private theorem difference_scope (left right M : ℕ) (hL : left < M) (hR : right < M) :
    (FormulaSignSlotRadialFormalInput.difference left right).arity ≤ M := by
  simp only [FormulaSignSlotRadialFormalInput.difference, Term.arity]
  omega
private theorem positive_scope (t : Term) (w M : ℕ) (ht : t.arity ≤ M) (hw : w < M) :
    (positiveRow t w).arity ≤ M := by
  simp only [positiveRow, Term.arity, Term.square]
  omega
private theorem sumRows_scope (count M : ℕ) (rows : ℕ → Term) (h : ∀ i < count, (rows i).arity ≤ M) :
    (sumRows count rows).arity ≤ M := by
  apply SumSquares.arity_accumulate_le _ _ _ (Nat.zero_le _)
  simp only [List.forall_mem_map, List.mem_range]
  exact h

theorem circle_scope (side : Bool) (q : List Bool) : (circle side q).arity ≤ dimension q :=
  ((FormulaSignSlotRadialJointTermCopy.copy_scope false side _).trans
    (Nat.mul_le_mul_left 4 (CanonicalAuxiliaryCandidateCover.equation_scope (source side q)))).trans
      (Nat.mul_le_mul_left 4 (circle_lt_slots side q))
theorem radial_scope (q : List Bool) : (radial q).arity ≤ dimension q :=
  ((FormulaSignSlotRadialJointTermCopy.copy_scope true false _).trans
    (Nat.mul_le_mul_left 4 (FormulaSignSlotRadialFormalInput.scope (source true q)))).trans
      (Nat.mul_le_mul_left 4 (formal_le_slots q))
private theorem center_le_slots (q : List Bool) : centerCount q ≤ slots q := by
  have H := formal_le_slots q
  change spatialCount q + (centerCount q + 1) ≤ slots q at H
  omega
private theorem old_le_slots (q : List Bool) : oldCount q ≤ slots q := by
  have H := formal_le_slots q
  change oldCount q + centerCount q + 1 + (centerCount q + 1) ≤ slots q at H
  omega

theorem centerSquares_scope (q : List Bool) : (centerSquares q).arity ≤ dimension q := by
  apply sumRows_scope
  intro i hi
  exact difference_scope _ _ _ (centerVariable_lt q ⟨i, hi⟩)
    (column_lt q 0 i (by decide) (hi.trans_le (center_le_slots q)))
theorem anchorSquares_scope (q : List Bool) : (anchorSquares q).arity ≤ dimension q := by
  apply sumRows_scope
  intro i hi
  exact difference_scope _ _ _ (column_lt q 2 i (by decide) (hi.trans_le (old_le_slots q)))
    (column_lt q 1 i (by decide) (hi.trans_le (old_le_slots q)))
theorem radiusRow_scope (q : List Bool) : (radiusRow q).arity ≤ dimension q :=
  positive_scope _ _ _ (Nat.succ_le_of_lt (radiusVariable_lt q)) (radiusWitness_lt q)
theorem gapRow_scope (q : List Bool) : (gapRow q).arity ≤ dimension q :=
  positive_scope _ _ _ (difference_scope _ _ _ (boundVariable_lt q) (radiusVariable_lt q)) (gapWitness_lt q)
theorem scope (q : List Bool) : (equation q).arity ≤ dimension q := by
  simp only [equation, Term.arity, Term.square, max_self]
  exact max_le (max_le (circle_scope false q) (circle_scope true q))
    (max_le (radial_scope q) (max_le (centerSquares_scope q) (max_le (anchorSquares_scope q)
      (max_le (radiusRow_scope q) (gapRow_scope q)))))

noncomputable def polynomial (q : List Bool) := (equation q).finitePolynomial (dimension q)
noncomputable def budget (q : List Bool) := (equation q).toData.size
theorem budget_unary : UnaryFn budget := (UnaryFn.length equation_FP).of_eq (fun q => Data.length_toBits (equation q).toData)
theorem polynomial_degree (q : List Bool) : (polynomial q).totalDegree ≤ budget q :=
  (Term.totalDegree_finitePolynomial _ _).trans (Term.degreeBound_le_dataSize _)
theorem polynomial_mass (q : List Bool) : LeanCanny.Algebra.MvMass.mass (polynomial q) ≤ 2 ^ budget q :=
  Term.finitePolynomial_mass _ _

end LeanCanny.Encoding.FormulaSignSlotRadialJointCore
