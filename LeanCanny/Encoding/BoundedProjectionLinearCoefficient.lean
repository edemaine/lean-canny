/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalProjection
public import LeanCanny.ETR.TubeLinearCoefficientSpace

/-! # Native coefficients of the retained projection row

The shared linear coefficient engine reads the actual fixed-width separating
weights. Its only retained-parameter coefficient is X on the homogenizing
coordinate; spatial coefficients are the negated weights.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionLinearCoefficient
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation MvPolynomial BoundedFullWriter Brackets
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def ell (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : ℕ) : ℤ :=
  FixedWidthQuery.entry (fun c => P.dim c + 4) (BoundedCriticalSeparator.width P) record c (i - 1)

def readIndex (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNat.sub (pair (pairSnd q) (BinaryNatCode.encode 1)))

theorem readIndex_mem_FP : readIndex ∈ FP :=
  mem_FP_pair pairFst_mem_FP
    (mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP)

noncomputable def read (P : Readers) (record : List Bool → List Bool) (q : List Bool) : List Bool :=
  (Codec.integer (ell P record (pairFst q) (Nat.fromBitsLE (pairSnd q)))).toBits

theorem read_mem_FP {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP) :
    read P record ∈ FP := by
  have hs := mem_FP_comp readIndex_mem_FP
    (FixedWidthQuery.read_mem_FP (h.dim.add (UnaryFn.const 4)) (BoundedCriticalSeparator.width_unary h) hr)
  have hn := BinaryFn.fromBits hs
  have he := Codec.taggedOne_mem_FP 0 (Codec.natural_toBits_mem_FP hn)
  apply mem_FP_of_eq he
  intro q
  have hp : FixedWidthQuery.read (fun c => P.dim c + 4) (BoundedCriticalSeparator.width P) record (readIndex q) =
      BinaryNatCode.encode (FixedWidthQuery.entry (fun c => P.dim c + 4) (BoundedCriticalSeparator.width P)
        record (pairFst q) (Nat.fromBitsLE (pairSnd q) - 1)) := by
    simpa only [readIndex, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      FixedWidthQuery.read_packet (fun c => P.dim c + 4) (BoundedCriticalSeparator.width P) record
        (pairFst q) (Nat.fromBitsLE (pairSnd q) - 1)
  simp only [Function.comp_apply, hp, BinaryNatCode.encode, Nat.fromBitsLE_bits, read, ell,
    Codec.integer, Codec.taggedOne_toBits]

noncomputable def polynomial (P : Readers) (record : List Bool → List Bool) (c : List Bool) :=
  LinearCoefficientBits.polynomial (fun c => P.dim c + 5) (TubeLinear.scalar (ell P record)) c

theorem polynomial_eq (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (q : Fin (P.dim c + 4) → MvPolynomial (Fin (P.dim c + 4)) ℤ) (d : Fin (P.dim c + 4) → ℕ) :
    polynomial P record c = LinearProjectionSystem.rows q d
      (fun i => (BoundedCriticalSeparator.weight P record c i.val : ℤ)) 0 := by
  have hn : (AffineCoordinateSystem.layout : Option (Fin (P.dim c + 4)) ≃ Fin (P.dim c + 4 + 1)) none = 0 := by
    apply Fin.ext
    exact HomogenizationLayout.variableEquiv_none (Equiv.refl _)
  have hs (i : Fin (P.dim c + 4)) :
      (AffineCoordinateSystem.layout : Option (Fin (P.dim c + 4)) ≃ Fin (P.dim c + 4 + 1)) (some i) = i.succ := by
    apply Fin.ext
    exact HomogenizationLayout.variableEquiv_some (Equiv.refl _) i
  rw [polynomial, LinearCoefficientBits.polynomial_eq_sum, Fin.sum_univ_succ]
  simp only [TubeLinear.scalar, Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
    LinearProjectionSystem.rows, Fin.cons_zero, LinearProjectionSystem.nativeRow,
    map_add, map_mul, map_sum, rename_C, rename_X, hn, hs,
    ell, Nat.add_sub_cancel_right, FixedWidthQuery.entry, Fin.isLt, BoundedCriticalSeparator.weight,
    map_neg, sub_eq_add_neg]
  congr 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact neg_mul (C (Polynomial.C (BoundedCriticalSeparator.weight P record c i.val : ℤ)) :
    MvPolynomial (Fin (P.dim c + 5)) (Polynomial ℤ)) (X i.succ)

noncomputable def value (P : Readers) (record : List Bool → List Bool) (W : List Bool → ℕ)
    (degree modulus : List Bool → List Bool) : List Bool → List Bool :=
  LinearCoefficientBits.value (fun c => P.dim c + 5) W (TubeLinear.scalar (ell P record)) degree modulus

theorem evaluator {P : Readers} {record : List Bool → List Bool} {W : List Bool → ℕ}
    {degree modulus : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP) (hW : UnaryFn W)
    (hpos : ∀ c, 0 < W c) (hk : degree ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value P record W degree modulus) :=
  LinearCoefficientBits.evaluator (h.dim.add (UnaryFn.const 5)) hW hpos (TubeLinear.scalar (ell P record))
    degree modulus (TubeLinear.scalarValue (read P record) degree modulus) hm
    (SpaceFunction.ofFP _ (TubeLinear.scalarValue_mem_FP (read_mem_FP h hr) hk hm))
    (fun c i _ => TubeLinear.scalarValue_packet (ell P record) (read P record) degree modulus c i
      (by simp only [read, pairFst_pair, pairSnd_pair, Nat.fromBitsLE_bits, BinaryNatCode.encode]))

end LeanCanny.Encoding.BoundedProjectionLinearCoefficient
