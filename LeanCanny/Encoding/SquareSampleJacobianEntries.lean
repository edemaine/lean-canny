/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleJacobianSource
public import LeanCanny.Algebra.FixedWidthDerivativeBinarySpace
public import LeanCanny.Algebra.FixedWidthCriticalSpace
public import LeanCanny.Algebra.HomogenizationPolynomialSpace

/-! # Native coefficients of square system Jacobian entries

Each selected partial uses one coefficient of the actual system row.
The canonical source-row reader remains charged.
Binary degree guards handle arbitrary requested derivative exponent widths.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleJacobianEntries
open LeanCanny.Algebra LeanCanny.Computation FixedWidthPolynomial MatrixPower
open SquareSampleInput (Inputs)
open SquareSampleSource (count)

open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible]
  SquareSampleSource.width HomogenizationPolynomialBits.integerValue FixedWidthDerivativeBits.value

def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def target (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
theorem row_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_FP : col ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem target_FP : target ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def atIndex (F : Inputs) (u : List Bool) (i : ℕ) : Fin (count F u) :=
  ⟨min i (count F u - 1), by have := SquareSampleSource.count_pos F u; omega⟩

theorem atIndex_valid (F : Inputs) (u : List Bool) (i : Fin (count F u)) : atIndex F u i.val = i := by
  apply Fin.ext
  exact Nat.min_eq_left (show i.val ≤ count F u - 1 by have := i.isLt; omega)

def selected (F : Inputs) (context bits : List Bool → List Bool) (q : List Bool) : Fin (count F (context (pairFst q))) :=
  atIndex F (context (pairFst q)) (Nat.fromBitsLE (bits q))
theorem selected_unary {F : Inputs} (h : F.Access) {context bits : List Bool → List Bool}
    (hc : context ∈ FP) (hb : bits ∈ FP) : UnaryFn (fun q => (selected F context bits q).val) :=
  UnaryFn.fromBitsLE_min hb (((SquareSampleSource.count_unary h).comp
    (mem_FP_comp pairFst_mem_FP hc)).sub (UnaryFn.const 1))

noncomputable def integerData (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (c : List Bool) (i j r : ℕ) : ℤ :=
  (MvPolynomial.pderiv (atIndex F (context c) j) (F.system (context c) (atIndex F (context c) i))).coeff
    (RationalSubstitution.Indexed.exponentVector (count F (context c)) (entry (W c) r))

theorem integerData_valid (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (c : List Bool) (i j : Fin (count F (context c))) (r : ℕ) :
    integerData F context W c i.val j.val r =
      (SquareSampleJacobianSource.matrix F (context c) i j).coeff
        (RationalSubstitution.Indexed.exponentVector (count F (context c)) (entry (W c) r)) := by
  unfold integerData
  rw [atIndex_valid, atIndex_valid]
  rfl

noncomputable def reader (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (row : (c : List Bool) → Fin (count F (context c))) (modulus : List Bool → List Bool) : List Bool → List Bool :=
  HomogenizationPolynomialBits.integerValue (count F ∘ context) W (fun c => F.system (context c) (row c)) modulus

theorem reader_evaluator {F : Inputs} (h : F.Access) {context : List Bool → List Bool} (hctx : context ∈ FP)
    {W : List Bool → ℕ} (hW : UnaryFn W)
    (r : (c : List Bool) → Fin (count F (context c))) (hr : UnaryFn (fun c => (r c).val))
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : SpaceFunction (reader F context W r modulus) := by
  unfold reader HomogenizationPolynomialBits.integerValue
  exact SquareSampleInput.row_evaluator h (mem_FP_comp pairFst_mem_FP hctx)
    (hW.comp pairFst_mem_FP) (fun q => r (pairFst q)) (hr.comp pairFst_mem_FP)
    pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm)

noncomputable def value (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits ((integerData F context W (pairFst q) (Nat.fromBitsLE (row q)) (Nat.fromBitsLE (col q))
    (Nat.fromBitsLE (target q)) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

theorem evaluator {F : Inputs} (h : F.Access) {context : List Bool → List Bool} (hc : context ∈ FP)
    {W : List Bool → ℕ} (hW : UnaryFn W) {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (value F context W modulus) := by
  let base := context ∘ pairFst
  have hb : base ∈ FP := mem_FP_comp pairFst_mem_FP hc
  have E := reader_evaluator h hb ((SquareSampleSource.width_unary h).comp hb)
    (selected F context row) (selected_unary h hc row_FP) (mem_FP_comp pairFst_mem_FP hm)
  have H := FixedWidthDerivativeBits.evaluator_binary_degree (fun q => count F (base q))
    (SquareSampleSource.width F ∘ base) (W ∘ pairFst) (F.degree ∘ base)
    (fun q => (selected F context col q).val) target (BinaryNat.succ ∘ modulus ∘ pairFst) E
    ((SquareSampleSource.count_unary h).comp hb)
    ((SquareSampleSource.width_unary h).comp hb) (hW.comp pairFst_mem_FP)
    ((h.degree).comp hb) (selected_unary h hc col_FP) target_FP
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP)
  refine H.congr (funext fun q => ?_)
  have HP := FixedWidthDerivativeBits.packet (fun q => count F (base q))
    (SquareSampleSource.width F ∘ base) (W ∘ pairFst) (F.degree ∘ base)
    (fun q => (selected F context col q).val) target (BinaryNat.succ ∘ modulus ∘ pairFst) (Equiv.refl _)
    (reader F base (SquareSampleSource.width F ∘ base) (selected F context row) (modulus ∘ pairFst))
    q (F.system (base q) (selected F context row q)) (selected F context col q)
    (Nat.fromBitsLE (modulus (pairFst q)) + 1) rfl rfl (F.degree_pos (base q))
    (SquareSampleJacobianSource.source_degree F (base q) (selected F context row q))
    (SquareSampleSource.degree_lt_width F (base q)) (BinaryNat.succ_eq_bits _)
    (fun r => HomogenizationPolynomialBits.integer_packet _ _ _ _ q r)
  rw [FixedWidthCriticalBits.exponent_eq_native, nativeExponent_refl] at HP
  dsimp only [Function.comp_def, value, integerData, selected, base, SquareSampleSource.count] at HP ⊢
  exact HP

theorem packet (F : Inputs) (context : List Bool → List Bool) (W : List Bool → ℕ)
    (modulus : List Bool → List Bool) (c : List Bool) (i j : Fin (count F (context c))) (r : ℕ) :
    value F context W modulus (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) =
        residueBits (((SquareSampleJacobianSource.matrix F (context c) i j).coeff
          (RationalSubstitution.Indexed.exponentVector (count F (context c)) (entry (W c) r)) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold value
  apply congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
  · simp only [row, col, target, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, integerData_valid]
  · rw [pairFst_pair]

end LeanCanny.Encoding.SquareSampleJacobianEntries
