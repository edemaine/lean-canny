/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedRules
/-! # Supplied rule numeric metadata is total native input syntax -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedRules
open LeanCanny.Algebra LeanCanny.Computation MatrixPower LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def offset {F : Inputs} (S : Source F) (q : List Bool) := FlatAffineExceptionalFrozenAdvice.countMask (maskWord S q)
def coarseMask {F : Inputs} (S : Source F) (q : List Bool) := FrozenCoordinatePermutationBits.eraseBit
  (pair (BinaryNatCode.encode (S.height (S.input q)).val) (maskWord S q))
noncomputable def coarseOffset {F : Inputs} (S : Source F) (q : List Bool) := FlatAffineExceptionalFrozenAdvice.countMask (coarseMask S q)

theorem offset_unary {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : UnaryFn (offset S) :=
  FlatAffineExceptionalFrozenAdvice.countMask_unary.comp (maskWord_FP hF S hS)
theorem coarseMask_FP {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : coarseMask S ∈ FP := by
  have HH : BinaryFn (fun q => (S.height (S.input q)).val) := hS.height.comp hS.input
  exact mem_FP_comp (mem_FP_pair HH.bits_mem_FP (maskWord_FP hF S hS)) FrozenCoordinatePermutationBits.eraseBit_FP
theorem coarseOffset_unary {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : UnaryFn (coarseOffset S) :=
  FlatAffineExceptionalFrozenAdvice.countMask_unary.comp (coarseMask_FP hF S hS)

theorem offset_eq {F : Inputs} (S : Source F) (q : List Bool) : offset S q = (frozen S q).card := by
  rw [offset, maskWord_eq, FlatAffineExceptionalFrozenAdvice.countMask_mask]
theorem coarseMask_eq {F : Inputs} (S : Source F) (q : List Bool) : coarseMask S q = FrozenCoordinatePermutationBits.mask (coarseFrozen S q) := by
  rw [coarseMask, maskWord_eq, FrozenCoordinatePermutationBits.eraseBit_mask]
  rfl
theorem coarseOffset_eq {F : Inputs} (S : Source F) (q : List Bool) : coarseOffset S q = (coarseFrozen S q).card := by
  rw [coarseOffset, coarseMask_eq, FlatAffineExceptionalFrozenAdvice.countMask_mask]

def inverseFree {F : Inputs} (S : Source F) (q : List Bool) := SuppliedFrozenMaskBits.inverse (arity F (S.input q)) (maskWord S q) (S.free (S.input q)).val
def inverseCoarseHeight {F : Inputs} (S : Source F) (q : List Bool) := SuppliedFrozenMaskBits.inverse (arity F (S.input q)) (coarseMask S q) (S.height (S.input q)).val

theorem inverseFree_FP {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : inverseFree S ∈ FP :=
  SuppliedFrozenMaskBits.inverse_FP _ ((FlatAffineFullSourceTower.arity_unary hF).comp hS.input) _ (maskWord_FP hF S hS) _ (hS.free.comp hS.input)
theorem inverseCoarseHeight_FP {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : inverseCoarseHeight S ∈ FP :=
  SuppliedFrozenMaskBits.inverse_FP _ ((FlatAffineFullSourceTower.arity_unary hF).comp hS.input) _ (coarseMask_FP hF S hS) _ (hS.height.comp hS.input)

theorem inverseFree_eq {F : Inputs} (S : Source F) (q : List Bool) : inverseFree S q = BinaryNatCode.encode ((order S q).symm (S.free (S.input q))).val := by
  rw [inverseFree, SuppliedFrozenMaskBits.inverse_packet, maskWord_eq, SuppliedFrozenMaskBits.selected_mask]
  rfl

theorem inverseCoarseHeight_eq {F : Inputs} (S : Source F) (q : List Bool) : inverseCoarseHeight S q = BinaryNatCode.encode ((coarseOrder S q).symm (S.height (S.input q))).val := by
  rw [inverseCoarseHeight, SuppliedFrozenMaskBits.inverse_packet, coarseMask_eq, SuppliedFrozenMaskBits.selected_mask]
  rfl

theorem objective_binary {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : BinaryFn (fun q => (critical S q).objective) := by
  have HI : BinaryFn (fun q => ((order S q).symm (S.free (S.input q))).val) :=
    (BinaryFn.fromBits (inverseFree_FP hF S hS)).of_eq (fun q => by rw [inverseFree_eq]; exact Nat.fromBitsLE_bits _)
  exact (HI.sub (BinaryFn.ofUnary (offset_unary hF S hS))).of_eq (fun q => by rw [offset_eq]; rfl)

theorem coarseObjective_binary {F : Inputs} (hF : F.Access) (S : Source F) (hS : Access S) : BinaryFn (fun q => (coarse S q).objective) := by
  have HI : BinaryFn (fun q => ((coarseOrder S q).symm (S.height (S.input q))).val) :=
    (BinaryFn.fromBits (inverseCoarseHeight_FP hF S hS)).of_eq (fun q => by rw [inverseCoarseHeight_eq]; exact Nat.fromBitsLE_bits _)
  exact (HI.sub (BinaryFn.ofUnary (coarseOffset_unary hF S hS))).of_eq (fun q => by rw [coarseOffset_eq]; rfl)
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedRules
