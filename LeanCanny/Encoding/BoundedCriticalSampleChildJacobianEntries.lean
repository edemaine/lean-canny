/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildJacobianSource
public import LeanCanny.Encoding.BoundedCriticalSampleJointWidth
public import LeanCanny.Algebra.FixedWidthDerivativeBinarySpace
public import LeanCanny.Algebra.FixedWidthCriticalSpace

/-! # Native coefficients of the joint Jacobian entries

The selected row is read from the original joint source. A native binary
degree guard and one coefficient call compute its selected partial. Context
extraction and exponent widths are supplied by native metadata readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildJacobianEntries
open LeanCanny.Algebra LeanCanny.Computation FixedWidthPolynomial MatrixPower
open BoundedCriticalSampleChildSource (Inputs)
open BoundedCriticalSampleChildParameters (system)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleJointSource.system BoundedCriticalSampleJointSource.degree
  BoundedCriticalSampleJointSource.width BoundedCriticalSampleJointWidth.value
  HomogenizationPolynomialBits.integerValue FixedWidthDerivativeBits.value

def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def target (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
theorem row_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_FP : col ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem target_FP : target ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def selected (F : Inputs) (context bits : List Bool → List Bool) (q : List Bool) : Fin (BoundedCriticalSampleChildSource.count F (context (pairFst q))) :=
  ⟨min (Nat.fromBitsLE (bits q)) (F.dim (context (pairFst q))), by unfold BoundedCriticalSampleChildSource.count; omega⟩
theorem selected_unary {F : Inputs} (h : F.PolyTime) {context bits : List Bool → List Bool}
    (hc : context ∈ FP) (hb : bits ∈ FP) : UnaryFn (fun q => (selected F context bits q).val) :=
  UnaryFn.fromBitsLE_min hb ((h.dim.comp hc).comp pairFst_mem_FP)

noncomputable def integerData (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (c : List Bool) (i j r : ℕ) : ℤ :=
  (MvPolynomial.pderiv ⟨min j (F.dim (context c)), by omega⟩
    (system F (context c) ⟨min i (F.dim (context c)), by omega⟩)).coeff
      (RationalSubstitution.Indexed.exponentVector (BoundedCriticalSampleChildSource.count F (context c)) (entry (W c) r))

theorem integerData_valid (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (c : List Bool) (i j : Fin (BoundedCriticalSampleChildSource.count F (context c))) (r : ℕ) :
    integerData F context W c i.val j.val r =
      (BoundedCriticalSampleChildJacobianSource.matrix F (context c) i j).coeff
        (RationalSubstitution.Indexed.exponentVector (BoundedCriticalSampleChildSource.count F (context c)) (entry (W c) r)) := by
  have hi : (⟨min i.val (F.dim (context c)), by unfold BoundedCriticalSampleChildSource.count; omega⟩ : Fin (BoundedCriticalSampleChildSource.count F (context c))) = i := by
    apply Fin.ext
    exact Nat.min_eq_left (show i.val ≤ F.dim (context c) by have := i.isLt; unfold BoundedCriticalSampleChildSource.count at this; omega)
  have hj : (⟨min j.val (F.dim (context c)), by unfold BoundedCriticalSampleChildSource.count; omega⟩ : Fin (BoundedCriticalSampleChildSource.count F (context c))) = j := by
    apply Fin.ext
    exact Nat.min_eq_left (show j.val ≤ F.dim (context c) by have := j.isLt; unfold BoundedCriticalSampleChildSource.count at this; omega)
  unfold integerData
  rw [hi, hj]
  rfl

noncomputable def value (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits ((integerData F context W (pairFst q) (Nat.fromBitsLE (row q)) (Nat.fromBitsLE (col q))
    (Nat.fromBitsLE (target q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

theorem evaluator {F : Inputs} (h : F.PolyTime) {context : List Bool → List Bool} (hc : context ∈ FP)
    {W : List Bool → ℕ} (hW : UnaryFn W) {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (value F context W modulus) := by
  let base := context ∘ pairFst
  have hb : base ∈ FP := mem_FP_comp pairFst_mem_FP hc
  have E := BoundedCriticalSampleJointWidth.evaluator h.parent F.term h.term h.offset h.dim h.directionWidth
    ((BoundedCriticalSampleJointSource.width_unary h.parent F.term h.term).comp hb) h.direction F.pivot h.pivot hb
    (selected F context row) (selected_unary h hc row_FP) (mem_FP_comp pairFst_mem_FP hm) h.arity
  have H := FixedWidthDerivativeBits.evaluator_binary_degree (fun q => BoundedCriticalSampleChildSource.count F (base q))
    (BoundedCriticalSampleJointSource.width F.parent F.term ∘ base) (W ∘ pairFst)
    (BoundedCriticalSampleJointSource.degree F.parent F.term ∘ base)
    (fun q => (selected F context col q).val) target (BinaryNat.succ ∘ modulus ∘ pairFst) E
    ((BoundedCriticalSampleChildSource.count_unary h).comp hb)
    ((BoundedCriticalSampleJointSource.width_unary h.parent F.term h.term).comp hb) (hW.comp pairFst_mem_FP)
    ((BoundedCriticalSampleJointSource.degree_binary h.parent F.term h.term).comp hb)
    (selected_unary h hc col_FP) target_FP (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP)
  refine H.congr (funext fun q => ?_)
  have HP := FixedWidthDerivativeBits.packet (fun q => BoundedCriticalSampleChildSource.count F (base q))
    (BoundedCriticalSampleJointSource.width F.parent F.term ∘ base) (W ∘ pairFst)
    (BoundedCriticalSampleJointSource.degree F.parent F.term ∘ base)
    (fun q => (selected F context col q).val) target (BinaryNat.succ ∘ modulus ∘ pairFst) (Equiv.refl _)
    (BoundedCriticalSampleJointWidth.value F.parent F.term F.offset F.dim F.directionWidth
      (BoundedCriticalSampleJointSource.width F.parent F.term ∘ base) F.direction base F.pivot (selected F context row) (modulus ∘ pairFst))
    q (system F (base q) (selected F context row q)) (selected F context col q)
    (Nat.fromBitsLE (modulus (pairFst q)) + 1) rfl rfl
    (BoundedCriticalSampleJointSource.degree_pos F.parent F.term (base q))
    (BoundedCriticalSampleChildJacobianSource.source_degree F (base q) (selected F context row q))
    (BoundedCriticalSampleJointSource.degree_lt_width F.parent F.term (base q))
    (BinaryNat.succ_eq_bits _) (by
      intro r
      unfold BoundedCriticalSampleJointWidth.value
      exact HomogenizationPolynomialBits.integer_packet _ _ _ _ q r)
  rw [FixedWidthCriticalBits.exponent_eq_native, nativeExponent_refl] at HP
  simpa only [Function.comp_def, value, integerData, selected, base, BoundedCriticalSampleChildSource.count] using HP

theorem packet (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (modulus : List Bool → List Bool) (c : List Bool) (i j : Fin (BoundedCriticalSampleChildSource.count F (context c))) (r : ℕ) :
    value F context W modulus (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) =
        residueBits (((BoundedCriticalSampleChildJacobianSource.matrix F (context c) i j).coeff
          (RationalSubstitution.Indexed.exponentVector (BoundedCriticalSampleChildSource.count F (context c)) (entry (W c) r)) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold value
  apply congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
  · simp only [row, col, target, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, integerData_valid]
  · rw [pairFst_pair]

end LeanCanny.Encoding.BoundedCriticalSampleChildJacobianEntries
