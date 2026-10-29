/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceTower
public import LeanCanny.Computation.PolyTimeArithmetic

/-! # Native metadata for complete flat-system coefficient queries

The packet is `pair (pair source (pair row exponent)) modulusMinusOne`.
Binary row indices are capped before unary processing. Stage and spatial
indices, block offsets, pivots, and copy indices have native controls on all
raw inputs. A space-computed direction record retains the original source.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceRowQuery
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open FlatFullSourceTower (Inputs arity count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def rowWord (q : List Bool) : List Bool := pairFst (pairSnd (pairFst q))
def target (q : List Bool) : List Bool := pairSnd (pairSnd (pairFst q))
def modulus (q : List Bool) : List Bool := pairSnd q
def rawRow (q : List Bool) : ℕ := Nat.fromBitsLE (rowWord q)

theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem rowWord_FP : rowWord ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem target_FP : target ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := pairSnd_mem_FP

def Valid (F : Inputs) (q : List Bool) : Prop := rawRow q < count F (source q)
def rowIndex (F : Inputs) (q : List Bool) : ℕ := min (rawRow q) (count F (source q))
def stageIndex (F : Inputs) (q : List Bool) : ℕ := rowIndex F q / arity F (source q)
def localIndex (F : Inputs) (q : List Bool) : ℕ := rowIndex F q % arity F (source q)
def blockOffset (F : Inputs) (q : List Bool) : ℕ := stageIndex F q * arity F (source q)
def previousIndex (F : Inputs) (q : List Bool) : ℕ := (stageIndex F q - 1) * arity F (source q) + localIndex F q
def stageQuery (F : Inputs) (q : List Bool) : List Bool := FlatFullSourceTower.stage (source q) (stageIndex F q)
def pivotLocal (F : Inputs) (q : List Bool) : ℕ := (F.pivot (source q) (stageIndex F q)).val
def baseIndex (F : Inputs) (q : List Bool) : ℕ := blockOffset F q + pivotLocal F q

theorem arity_pos (F : Inputs) (q : List Bool) : 0 < arity F (source q) := by unfold arity; omega

theorem count_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => count F (source q)) :=
  (FlatFullSourceTower.count_unary h).comp source_FP
theorem arity_unary {F : Inputs} (h : F.Access) : UnaryFn (fun q => arity F (source q)) :=
  (FlatFullSourceTower.arity_unary h).comp source_FP
theorem rowIndex_unary {F : Inputs} (h : F.Access) : UnaryFn (rowIndex F) :=
  UnaryFn.fromBitsLE_min rowWord_FP (count_unary h)
theorem stageIndex_unary {F : Inputs} (h : F.Access) : UnaryFn (stageIndex F) :=
  (rowIndex_unary h).div (arity_unary h)
theorem localIndex_unary {F : Inputs} (h : F.Access) : UnaryFn (localIndex F) :=
  (rowIndex_unary h).mod (arity_unary h)
theorem blockOffset_unary {F : Inputs} (h : F.Access) : UnaryFn (blockOffset F) :=
  (stageIndex_unary h).mul (arity_unary h)
theorem previousIndex_unary {F : Inputs} (h : F.Access) : UnaryFn (previousIndex F) :=
  (((stageIndex_unary h).sub (UnaryFn.const 1)).mul (arity_unary h)).add (localIndex_unary h)

theorem stageQuery_FP {F : Inputs} (h : F.Access) : stageQuery F ∈ FP :=
  mem_FP_pair source_FP (BinaryFn.ofUnary (stageIndex_unary h)).bits_mem_FP

theorem pivotLocal_binary {F : Inputs} (h : F.Access) : BinaryFn (pivotLocal F) := by
  apply BinaryFn.of_eq (h.pivot.comp (stageQuery_FP h))
  intro q
  change (F.pivot (pairFst (stageQuery F q)) (Nat.fromBitsLE (pairSnd (stageQuery F q)))).val = _
  have h0 : pairFst (stageQuery F q) = source q := pairFst_pair _ _
  have h1 : Nat.fromBitsLE (pairSnd (stageQuery F q)) = stageIndex F q := by
    rw [stageQuery, FlatFullSourceTower.stage, pairSnd_pair, MacaulayBits.fromBits_encode]
  rw [h0, h1]
  rfl

theorem pivotLocal_lt (F : Inputs) (q : List Bool) : pivotLocal F q < arity F (source q) :=
  (F.pivot (source q) (stageIndex F q)).isLt

theorem pivotLocal_unary {F : Inputs} (h : F.Access) : UnaryFn (pivotLocal F) := by
  apply (UnaryFn.fromBitsLE_min (pivotLocal_binary h).bits_mem_FP (arity_unary h)).of_eq
  intro q
  rw [MacaulayBits.fromBits_encode, Nat.min_eq_left (pivotLocal_lt F q).le]

theorem baseIndex_unary {F : Inputs} (h : F.Access) : UnaryFn (baseIndex F) :=
  (blockOffset_unary h).add (pivotLocal_unary h)

theorem valid_FP {F : Inputs} (h : F.Access) : FPPred (Valid F) :=
  (BinaryFn.fromBits rowWord_FP).lt (BinaryFn.ofUnary (count_unary h))

def InFree (F : Inputs) (q : List Bool) : Prop := F.offset (stageQuery F q) ≤ localIndex F q ∧
  localIndex F q < F.offset (stageQuery F q) + F.dim (stageQuery F q)

theorem inFree_FP {F : Inputs} (h : F.Access) : FPPred (InFree F) := by
  have ho : BinaryFn (fun q => F.offset (stageQuery F q)) := h.offset.comp (stageQuery_FP h)
  have hd := BinaryFn.ofUnary (h.dim.comp (stageQuery_FP h))
  have hi := BinaryFn.ofUnary (localIndex_unary h)
  exact (ho.le hi).and (hi.lt (ho.add hd))

theorem rowIndex_of_valid (F : Inputs) (q : List Bool) (h : Valid F q) : rowIndex F q = rawRow q :=
  Nat.min_eq_left h.le

theorem localIndex_lt (F : Inputs) (q : List Bool) : localIndex F q < arity F (source q) :=
  Nat.mod_lt _ (arity_pos F q)

theorem split_row (F : Inputs) (q : List Bool) : blockOffset F q + localIndex F q = rowIndex F q := by
  unfold blockOffset localIndex stageIndex
  simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div (rowIndex F q) (arity F (source q))

theorem stageIndex_lt (F : Inputs) (q : List Bool) (h : Valid F q) : stageIndex F q < F.depth (source q) := by
  apply (Nat.div_lt_iff_lt_mul (arity_pos F q)).mpr
  rw [rowIndex_of_valid F q h]
  exact h

theorem block_fit (F : Inputs) (q : List Bool) (h : Valid F q) :
    blockOffset F q + arity F (source q) ≤ count F (source q) := by
  have H := Nat.mul_le_mul_right (arity F (source q)) (stageIndex_lt F q h)
  simpa only [Nat.succ_mul, blockOffset, count] using H

noncomputable def directionRecord (F : Inputs) : List Bool → List Bool := F.direction ∘ stageQuery F
theorem directionRecord_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (directionRecord F) :=
  h.direction.precompose _ (stageQuery_FP h)

noncomputable def prepare (F : Inputs) (q : List Bool) : List Bool := pair q (directionRecord F q)
theorem prepare_evaluator {F : Inputs} (h : F.Access) : SpaceFunction (prepare F) :=
  (directionRecord_evaluator h).withInput

end LeanCanny.Encoding.FlatFullSourceRowQuery
