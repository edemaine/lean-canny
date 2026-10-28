/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCoordinateSystem
public import LeanCanny.ETR.TubeLinearCoefficientSpace

/-! # Native coefficients of the affine coordinate equation

The extra row is `u X₀ - Xᵢ`. Its two scalar coefficients use the existing
streamed linear-row engine, with a native unit-coordinate reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCoordinateLinearBits
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR MvPolynomial
open scoped Classical BigOperators

def ell {N : List Bool → ℕ} (coordinate : (c : List Bool) → Fin (N c)) (c : List Bool) (i : ℕ) : ℤ :=
  if i = (coordinate c).val + 1 then 1 else 0

def read {N : List Bool → ℕ} (coordinate : (c : List Bool) → Fin (N c)) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) = (coordinate (pairFst q)).val + 1 then
    (Codec.integer 1).toBits else (Codec.integer 0).toBits

theorem read_FP {N : List Bool → ℕ} (coordinate : (c : List Bool) → Fin (N c))
    (hi : UnaryFn (fun c => (coordinate c).val)) : read coordinate ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).eq
    (BinaryFn.ofUnary ((hi.comp pairFst_mem_FP).add (UnaryFn.const 1)))).ite_mem_FP
      (constFn_mem_FP _) (constFn_mem_FP _)

noncomputable def polynomial (N : List Bool → ℕ) (coordinate : (c : List Bool) → Fin (N c)) (c : List Bool) :=
  LinearCoefficientBits.polynomial (fun c => N c + 1) (TubeLinear.scalar (ell coordinate)) c

theorem polynomial_eq (N : List Bool → ℕ) (coordinate : (c : List Bool) → Fin (N c)) (c : List Bool)
    (q : Fin (N c) → MvPolynomial (Fin (N c)) ℤ) (d : Fin (N c) → ℕ) :
    polynomial N coordinate c = AffineCoordinateSystem.rows q d (coordinate c) 0 := by
  have hn : (AffineCoordinateSystem.layout : Option (Fin (N c)) ≃ Fin (N c + 1)) none = 0 := by
    apply Fin.ext
    exact HomogenizationLayout.variableEquiv_none (Equiv.refl _)
  have hs (i : Fin (N c)) :
      (AffineCoordinateSystem.layout : Option (Fin (N c)) ≃ Fin (N c + 1)) (some i) = i.succ := by
    apply Fin.ext
    exact HomogenizationLayout.variableEquiv_some (Equiv.refl _) i
  rw [polynomial, LinearCoefficientBits.polynomial_eq_sum, Fin.sum_univ_succ]
  simp only [TubeLinear.scalar, Fin.val_zero, ite_true, Fin.val_succ, Nat.add_one_ne_zero, ite_false,
    ell, Nat.add_right_cancel_iff, ← Fin.ext_iff, AffineCoordinateSystem.rows, Fin.cons_zero,
    AffineCoordinateSystem.nativeRow, map_sub, map_mul, rename_C, rename_X, hn, hs]
  simp only [sub_eq_add_neg, add_right_inj]
  have he (i : Fin (N c)) :
      C (-Polynomial.C (if i = coordinate c then (1 : ℤ) else 0)) * X i.succ =
        (if i = coordinate c then -X i.succ else 0 : MvPolynomial (Fin (N c + 1)) (Polynomial ℤ)) := by
    by_cases hi : i = coordinate c
    · rw [ite_eq_left hi, ite_eq_left hi, Polynomial.C_1, MvPolynomial.C_neg, MvPolynomial.C_1]
      exact neg_one_mul (X i.succ)
    · rw [ite_eq_right hi, ite_eq_right hi, Polynomial.C_0, neg_zero, MvPolynomial.C_0, zero_mul]
  simp_rw [he]
  simp

noncomputable def value (N W : List Bool → ℕ) (coordinate : (c : List Bool) → Fin (N c))
    (parameter modulus : List Bool → List Bool) : List Bool → List Bool :=
  LinearCoefficientBits.value (fun c => N c + 1) W (TubeLinear.scalar (ell coordinate)) parameter modulus

theorem evaluator {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hpos : ∀ c, 0 < W c)
    (coordinate : (c : List Bool) → Fin (N c)) (hi : UnaryFn (fun c => (coordinate c).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value N W coordinate parameter modulus) :=
  LinearCoefficientBits.evaluator (hN.add (UnaryFn.const 1)) hW hpos (TubeLinear.scalar (ell coordinate))
    parameter modulus (TubeLinear.scalarValue (read coordinate) parameter modulus) hm
    (SpaceFunction.ofFP _ (TubeLinear.scalarValue_mem_FP (read_FP coordinate hi) hk hm))
    (fun c i _ => TubeLinear.scalarValue_packet (ell coordinate) (read coordinate) parameter modulus c i (by
      have hc : (coordinate (pairFst (pair c (BinaryNatCode.encode i)))).val = (coordinate c).val :=
        congrArg (fun z => (coordinate z).val) (pairFst_pair c (BinaryNatCode.encode i))
      simp only [read, ell, hc, pairSnd_pair, MacaulayBits.fromBits_encode]
      split_ifs <;> rfl))

end LeanCanny.Algebra.AffineCoordinateLinearBits
