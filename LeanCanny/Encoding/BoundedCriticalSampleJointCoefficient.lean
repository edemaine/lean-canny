/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleParameterRow
public import LeanCanny.Encoding.BoundedCriticalSampleJointCritical

/-! # Native coefficients of the complete joint candidate system

Row zero is the original parameter equation. Rows one through the block
dimension are the constructed critical equations in the common layout.
Parent-row access also works for an empty block. Invalid spatial rows or
pivots return zero. All routines use the original source and term readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleJointCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter FixedWidthPolynomial
open BoundedCriticalSampleBlockCritical (origin row target origin_FP row_FP target_FP)
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleParameterRow.value BoundedCriticalSampleJointCritical.value
  BoundedCriticalSampleBlockCriticalSource.polynomial BoundedCriticalSampleJointSource.width

def parentQuery (q : List Bool) : List Bool := pair (pair (origin q) (target q)) (pairSnd q)
def criticalQuery (q : List Bool) : List Bool :=
  pair (pair (origin q) (pair (BinaryNat.pred (row q)) (pairSnd q))) (target q)
theorem parentQuery_FP : parentQuery ∈ FP := mem_FP_pair (mem_FP_pair origin_FP target_FP) pairSnd_mem_FP
theorem criticalQuery_FP : criticalQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair origin_FP (mem_FP_pair
    (mem_FP_comp (f := row) (g := BinaryNat.pred) row_FP BinaryNat.pred_mem_FP) pairSnd_mem_FP)) target_FP

def valid (k b : List Bool → ℕ) (q : List Bool) : Prop :=
  Nat.fromBitsLE (row q) < k (origin q) + 1 ∧ b (origin q) < k (origin q)
instance (k b : List Bool → ℕ) (q : List Bool) : Decidable (valid k b q) := inferInstanceAs (Decidable (_ ∧ _))
theorem valid_pred {k b : List Bool → ℕ} (hk : UnaryFn k) (hb : BinaryFn b) : FPPred (valid k b) := by
  have K : BinaryFn (fun q => k (origin q)) := BinaryFn.ofUnary (hk.comp origin_FP)
  have B : BinaryFn (fun q => b (origin q)) := hb.comp origin_FP
  exact ((BinaryFn.fromBits row_FP).lt (K.add (BinaryFn.const 1))).and (B.lt K)

noncomputable def value (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (row q) = 0 then BoundedCriticalSampleParameterRow.value P read k (parentQuery q)
  else if valid k b q then BoundedCriticalSampleJointCritical.value P read o k w b bits (criticalQuery q) else []

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {o k w b : List Bool → ℕ} (ho : BinaryFn o) (hk : UnaryFn k) (hw : UnaryFn w) (hb : BinaryFn b)
    {bits : List Bool → List Bool} (hbits : bits ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P read o k w b bits) := by
  have H := (BinaryFn.fromBits row_FP).eq (BinaryFn.const 0)
  have L := (BoundedCriticalSampleParameterRow.evaluator h read hr hk ha).precompose parentQuery parentQuery_FP
  have R := (BoundedCriticalSampleJointCritical.evaluator h read hr ho hk hw hb hbits ha).precompose criticalQuery criticalQuery_FP
  exact (SpaceFunction.branch _ H.flag_mem_FP L
    (SpaceFunction.branch _ (valid_pred hk hb).flag_mem_FP R (SpaceFunction.ofFP _ (constFn_mem_FP [])))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem parent_packet (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (r m : ℕ) :
    value P read o k w b bits (pair (pair u (pair [] (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
      MatrixPower.residueBits (((IndexedMultivariateRational.parameter (k u)
        (BoundedCriticalRationalCoordinates.parameter P (pairFst u))).coeff
          (nativeExponent (Equiv.refl (Fin (k u + 1))) (BoundedCriticalSampleJointSource.width P read u) r) : ℤ) : ZMod (m + 1)) := by
  simpa only [value, row, pairFst_pair, pairSnd_pair, show Nat.fromBitsLE [] = 0 from rfl,
    ite_true, parentQuery, origin, target] using BoundedCriticalSampleParameterRow.packet P read k u r m

theorem packet (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (u : List Bool) (pivot : Fin (k u)) (hb : b u = pivot.val)
    (i : Fin (k u + 1)) (r m : ℕ) :
    value P read o k w b bits
      (pair (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r))) (BinaryNatCode.encode m)) =
        MatrixPower.residueBits (((BoundedCriticalSampleJointSource.system P read o k w bits u pivot i).coeff
          (nativeExponent (Equiv.refl (Fin (k u + 1))) (BoundedCriticalSampleJointSource.width P read u) r) : ℤ) : ZMod (m + 1)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact parent_packet P read o k w b bits u r m
  · have hv : valid k b (pair (pair u (pair (BinaryNatCode.encode j.succ.val) (BinaryNatCode.encode r)))
        (BinaryNatCode.encode m)) := by
      simp only [valid, row, origin, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hb]
      exact ⟨j.succ.isLt, pivot.isLt⟩
    have hne : Nat.fromBitsLE (row (pair (pair u (pair (BinaryNatCode.encode j.succ.val) (BinaryNatCode.encode r)))
        (BinaryNatCode.encode m))) ≠ 0 := by
      simp only [row, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.val_succ]
      omega
    rw [value, ite_eq_right hne, ite_eq_left hv]
    have H := BoundedCriticalSampleJointCritical.packet P read o k w b bits u pivot j hb r m
    simpa only [criticalQuery, row, origin, target, pairFst_pair, pairSnd_pair, BinaryNat.pred_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.val_succ, Nat.add_sub_cancel,
      BoundedCriticalSampleJointSource.system, RetainedParameterSystem.system, Fin.cons_succ] using H

theorem invalid_spatial (P : Readers) (read : List Bool → List Bool) (o k w b : List Bool → ℕ)
    (bits : List Bool → List Bool) (q : List Bool) (h0 : Nat.fromBitsLE (row q) ≠ 0) (hq : ¬ valid k b q) :
    value P read o k w b bits q = [] := by
  rw [value, ite_eq_right h0, ite_eq_right hq]

end LeanCanny.Encoding.BoundedCriticalSampleJointCoefficient
