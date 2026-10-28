/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentParameterRow
public import LeanCanny.Encoding.BoundedCriticalSampleJointCoefficient
public import LeanCanny.Encoding.RationalParentJointCritical

/-! # Native coefficients of the complete joint candidate system

Row zero is the original parameter equation. Rows one through the block
dimension are the constructed critical equations in the common layout.
Parent-row access also works for an empty block. Invalid spatial rows or
pivots return zero. The source remains implicit, and the direction record may require polynomial space.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentJointCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open BoundedCriticalSampleBlockCritical (origin row target origin_FP row_FP target_FP)
open RationalParentJointSource (Inputs)
open BoundedCriticalSampleJointCoefficient
open scoped Classical
attribute [local irreducible] RationalParentParameterRow.value RationalParentJointCritical.value
  RationalParentFullBlockCriticalSource.polynomial RationalParentJointSource.width

noncomputable def value (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (row q) = 0 then RationalParentParameterRow.value F (parentQuery q)
  else if valid F.block.dim b q then RationalParentJointCritical.value F w b bits (criticalQuery q) else []

theorem evaluator {F : Inputs} (h : F.Access)
    {w b : List Bool → ℕ} (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (E : SpaceFunction bits)
    (htS : ∀ u, (TermView.term (F.block.source.source u)).arity ≤ F.block.source.dim u) : SpaceFunction (value F w b bits) := by
  have H := (BinaryFn.fromBits row_FP).eq (BinaryFn.const 0)
  have L := (RationalParentParameterRow.evaluator h).precompose parentQuery parentQuery_FP
  have R := (RationalParentJointCritical.evaluator h hw hb E htS).precompose criticalQuery criticalQuery_FP
  exact (SpaceFunction.branch _ H.flag_mem_FP L
    (SpaceFunction.branch _ (valid_pred h.block.dim hb).flag_mem_FP R (SpaceFunction.ofFP _ (constFn_mem_FP [])))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem parent_packet (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (r m : ℕ) :
    value F w b bits (pair (pair u (pair [] (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
      MatrixPower.residueBits (((IndexedMultivariateRational.parameter (F.block.dim u)
        (F.parent.polynomial u)).coeff
          (nativeExponent (Equiv.refl (Fin (F.block.dim u + 1))) (RationalParentJointSource.width F u) r) : ℤ) : ZMod (m + 1)) := by
  simpa only [value, row, pairFst_pair, pairSnd_pair, show Nat.fromBitsLE [] = 0 from rfl,
    ite_true, parentQuery, origin, target] using RationalParentParameterRow.packet F u r m

theorem packet (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (pivot : Fin (F.block.dim u)) (hb : b u = pivot.val)
    (i : Fin (F.block.dim u + 1)) (r m : ℕ) :
    value F w b bits
      (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
        MatrixPower.residueBits (((RationalParentJointSource.system F w bits u pivot i).coeff
          (nativeExponent (Equiv.refl (Fin (F.block.dim u + 1))) (RationalParentJointSource.width F u) r) : ℤ) : ZMod (m + 1)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact parent_packet F w b bits u r m
  · have hv : valid F.block.dim b (pair (pair u (pair (BinaryNatCode.encode j.succ.val) (BinaryNatCode.encode r)))
        (BinaryNatCode.encode m)) := by
      simp only [valid, row, origin, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hb]
      exact ⟨j.succ.isLt, pivot.isLt⟩
    have hne : Nat.fromBitsLE (row (pair (pair u (pair (BinaryNatCode.encode j.succ.val) (BinaryNatCode.encode r)))
        (BinaryNatCode.encode m))) ≠ 0 := by
      simp only [row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.val_succ]
      omega
    rw [value, ite_eq_right hne, ite_eq_left hv]
    have H := RationalParentJointCritical.packet F w b bits u pivot j hb r m
    simpa only [criticalQuery, row, origin, target, pairFst_pair, pairSnd_pair, BinaryNat.pred_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.val_succ, Nat.add_sub_cancel,
      RationalParentJointSource.system, RetainedParameterSystem.system, Fin.cons_succ] using H

theorem invalid_spatial (F : Inputs) (w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) (h0 : Nat.fromBitsLE (row q) ≠ 0) (hq : ¬ valid F.block.dim b q) :
    value F w b bits q = [] := by
  rw [value, ite_eq_right h0, ite_eq_right hq]

end LeanCanny.Encoding.RationalParentJointCoefficient
