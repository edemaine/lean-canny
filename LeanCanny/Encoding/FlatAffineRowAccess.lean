/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineRowLayout
public import LeanCanny.Computation.SpaceFunctionSelect

/-! # Native metadata and charged records for affine row dispatch -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineRowAccess
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineRowLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {F : Inputs} (h : F.Access) {row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)}
  (hr : UnaryFn (fun u => (row u).val))

include h hr in
theorem stage_unary : UnaryFn (stage F row) := hr.div (FlatAffineFullSourceTower.stageWidth_unary h)
include h hr in
theorem slot_unary : UnaryFn (slot F row) := hr.mod (FlatAffineFullSourceTower.stageWidth_unary h)
include h hr in
theorem offset_unary : UnaryFn (offset F row) := (stage_unary h hr).mul (FlatAffineFullSourceTower.stageWidth_unary h)
include h hr in
theorem spatial_unary : UnaryFn (fun u => (spatial F row u).val) :=
  (slot_unary h hr).min ((FlatAffineFullSourceTower.arity_unary h).sub (UnaryFn.const 1))
include h hr in
theorem height_unary : UnaryFn (fun u => (height F row u).val) :=
  (((slot_unary h hr).sub (FlatAffineFullSourceTower.arity_unary h)).sub (UnaryFn.const 1)).min
    ((FlatAffineFullSourceTower.arity_unary h).sub (UnaryFn.const 1))

include h hr in
theorem stageQuery_FP : (fun u => FlatAffineFullSourceTower.stage u (stage F row u)) ∈ FP :=
  mem_FP_pair id_mem_FP (BinaryFn.ofUnary (stage_unary h hr)).bits_mem_FP

include h hr in
theorem levelQuery_FP : (fun u => FlatAffineFullSourceTower.levelQuery u (stage F row u) (height F row u).val) ∈ FP :=
  mem_FP_pair (stageQuery_FP h hr) (BinaryFn.ofUnary (height_unary h hr)).bits_mem_FP

include h hr in
theorem direction_evaluator : SpaceFunction (directionRecord F row) := h.direction.precompose _ (stageQuery_FP h hr)
include h hr in
theorem level_evaluator : SpaceFunction (levelRecord F row) := h.level.precompose _ (levelQuery_FP h hr)

theorem normal_FP : FlatAffineFullSourceTower.normal ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP

theorem constant_FP : FlatAffineFullSourceTower.constant ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

theorem left_FP : FlatAffineFullSourceTower.left ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP

theorem right_FP : FlatAffineFullSourceTower.right ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP

theorem tag_binary : BinaryFn FlatAffineFullSourceTower.tag :=
  BinaryFn.fromBits (take_mem_FP (drop_mem_FP pairFst_mem_FP (UnaryFn.const 1)) (UnaryFn.const 2))

/-- A counter reader is clamped before unary arithmetic, including malformed words. -/
def counter (N : List Bool → ℕ) (q : List Bool) : ℕ := min (Nat.fromBitsLE (pairSnd q)) (N (pairFst q))

theorem counter_unary {N : List Bool → ℕ} (hN : UnaryFn N) : UnaryFn (counter N) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP (hN.comp pairFst_mem_FP)

variable (F row)

def currentSelected (q : List Bool) : ℕ :=
  min (offset F row (pairFst q) + counter (arity F) q) (FlatAffineFullSourceTower.count F (pairFst q))
def multiplierSelected (q : List Bool) : ℕ :=
  min (offset F row (pairFst q) + arity F (pairFst q) + counter (fun u => arity F u + 1) q)
    (FlatAffineFullSourceTower.count F (pairFst q))

def oldSelected (field : List Bool → List Bool) (q : List Bool) : ℕ :=
  min (min (Nat.fromBitsLE (field (levelRecord F row (pairFst q)))) (stage F row (pairFst q) - 1) *
    FlatAffineFullSourceTower.stageWidth F (pairFst q) + counter (arity F) q)
      (FlatAffineFullSourceTower.count F (pairFst q))

variable {F row}

include h hr in
theorem currentSelected_unary : UnaryFn (currentSelected F row) :=
  (((offset_unary h hr).comp pairFst_mem_FP).add (counter_unary (FlatAffineFullSourceTower.arity_unary h))).min
    ((FlatAffineFullSourceTower.count_unary h).comp pairFst_mem_FP)

include h hr in
theorem multiplierSelected_unary : UnaryFn (multiplierSelected F row) :=
  ((((offset_unary h hr).add (FlatAffineFullSourceTower.arity_unary h)).comp pairFst_mem_FP).add
    (counter_unary ((FlatAffineFullSourceTower.arity_unary h).add (UnaryFn.const 1)))).min
      ((FlatAffineFullSourceTower.count_unary h).comp pairFst_mem_FP)

include h hr in
theorem oldSelected_evaluator (field : List Bool → List Bool) (hf : field ∈ FP) :
    SpaceFunction (BinaryNatCode.encode ∘ oldSelected F row field) := by
  let origin : List Bool → List Bool := pairFst ∘ pairFst
  have ho : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  let refIndex (z : List Bool) := min (Nat.fromBitsLE (field (pairSnd z))) (stage F row (origin z) - 1)
  let selected (z : List Bool) := min (refIndex z * FlatAffineFullSourceTower.stageWidth F (origin z) +
    counter (arity F) (pairFst z)) (FlatAffineFullSourceTower.count F (origin z))
  have hRef : UnaryFn refIndex := UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP hf)
    (((stage_unary h hr).comp ho).sub (UnaryFn.const 1))
  have hSel : UnaryFn selected := ((hRef.mul ((FlatAffineFullSourceTower.stageWidth_unary h).comp ho)).add
    ((counter_unary (FlatAffineFullSourceTower.arity_unary h)).comp pairFst_mem_FP)).min
      ((FlatAffineFullSourceTower.count_unary h).comp ho)
  have H := ((level_evaluator h hr).precompose pairFst pairFst_mem_FP).withInput.postcompose
    (BinaryNatCode.encode ∘ selected) (BinaryFn.ofUnary hSel).bits_mem_FP
  exact H.congr (funext fun q => by
    simp only [oldSelected, selected, refIndex, origin, Function.comp_apply, pairFst_pair, pairSnd_pair])

end LeanCanny.Encoding.FlatAffineRowAccess
