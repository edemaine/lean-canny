/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeZeroSpace
public import LeanCanny.Encoding.FixedWidthQuery

/-! # Zero-source tube access from arbitrary fixed-width exponent queries

An FP guard rejects any coordinate exponent above four, forcing coefficient
zero by the actual degree theorem. Valid exponents are repacked for the sparse
source reader. Thus width changes cannot alias a large exponent to a nonzero
coefficient, even on malformed, short, or redundant binary words.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeZeroQuery
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower

noncomputable def exponent (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : Coordinate (n c) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => FixedWidthQuery.coordinate W target c (coordinateEquiv (n c) j).val)

noncomputable def coefficient (n W : List Bool → ℕ) (active target : List Bool → List Bool) (c : List Bool) : ℤ :=
  (TubePolynomial.integerPolynomial (0 : MvPolynomial (Fin (n c)) ℤ) (activeSet (n c) (active c))).coeff (exponent n W target c)

def Allowed (n W : List Bool → ℕ) (target : List Bool → List Bool) : List Bool → Prop :=
  FixedWidthQuery.Bounded (fun c => dimension (n c)) W target (fun _ => 4)

theorem dimension_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun c => dimension (n c)) :=
  (hn.add (TubeZero.constraintCount_unary hn)).add (UnaryFn.const 3)

theorem allowed_fppred {n W : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (ht : target ∈ FP) : FPPred (Allowed n W target) :=
  FixedWidthQuery.bounded_fppred (dimension_unary hn) hW (UnaryFn.const 4) ht

def repacked (n W : List Bool → ℕ) (active target : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthQuery.repack (fun c => dimension (n c)) W (TubeZero.size n active) (fun c => TubeZero.size n active c + 1) target

theorem repacked_mem_FP {n W : List Bool → ℕ} {active target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (ha : active ∈ FP) (ht : target ∈ FP) : repacked n W active target ∈ FP :=
  FixedWidthQuery.repack_mem_FP (dimension_unary hn) hW (TubeZero.size_unary hn ha)
    ((TubeZero.size_unary hn ha).add (UnaryFn.const 1)) ht

theorem padded_exponent (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    TubeZero.paddedExponent (n c) (exponent n W target c) i =
      FixedWidthQuery.entry (fun c => dimension (n c)) W target c i := by
  unfold TubeZero.paddedExponent FixedWidthQuery.entry
  split_ifs
  · simp only [exponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.apply_symm_apply]
  · rfl

theorem repacked_eq_code (n W : List Bool → ℕ) (active target : List Bool → List Bool) (c : List Bool) :
    repacked n W active target c = TubeZero.exponentCode n active c (exponent n W target c) := by
  unfold repacked FixedWidthQuery.repack TubeZero.exponentCode
  congr 1
  funext i
  exact (padded_exponent n W target c i).symm

theorem four_lt_size (n : List Bool → ℕ) (active : List Bool → List Bool) (c : List Bool) :
    4 < 2 ^ (TubeZero.size n active c + 1) := by
  have h := TubeZero.dimension_le_size n active c
  have hd : 5 ≤ dimension (n c) := by unfold dimension constraintCount; omega
  exact (show 4 < TubeZero.size n active c + 1 by omega).trans (Nat.lt_two_pow_self)

theorem child_correct (n W : List Bool → ℕ) (active target modulus : List Bool → List Bool) (c : List Bool)
    (h : Allowed n W target c) :
    TubeZero.value n active (repacked n W active target) modulus c =
      residueBits ((coefficient n W active target c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  apply TubeZero.value_eq_native n active (repacked n W active target) modulus c (exponent n W target c)
    (repacked_eq_code n W active target c)
  intro j
  have hj := h (coordinateEquiv (n c) j).val (coordinateEquiv (n c) j).isLt
  exact hj.trans_lt (four_lt_size n active c)

theorem coefficient_eq_zero_of_not_allowed (n W : List Bool → ℕ) (active target : List Bool → List Bool) (c : List Bool)
    (h : ¬ Allowed n W target c) : coefficient n W active target c = 0 := by
  by_contra hne
  apply h
  intro i hi
  let j := (coordinateEquiv (n c)).symm ⟨i, hi⟩
  have hj := MvPolynomial.monomial_le_degreeOf j (MvPolynomial.mem_support_iff.mpr hne)
  have hd := TubePolynomial.integer_polynomial_degree (0 : MvPolynomial (Fin (n c)) ℤ) (activeSet (n c) (active c))
  simp only [MvPolynomial.totalDegree_zero, max_eq_right (Nat.zero_le 2)] at hd
  have he := hj.trans ((MvPolynomial.degreeOf_le_totalDegree _ j).trans hd)
  simpa only [exponent, Finsupp.coe_equivFunOnFinite_symm, j, Equiv.apply_symm_apply] using he

noncomputable def value (n W : List Bool → ℕ) (active target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits ((coefficient n W active target c : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem evaluator (n W : List Bool → ℕ) (active target modulus : List Bool → List Bool)
    (hn : UnaryFn n) (hW : UnaryFn W) (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value n W active target modulus) := by
  classical
  let R := TubeZero.evaluator n active (repacked n W active target) modulus hn ha (repacked_mem_FP hn hW ha ht) hm
  let E := SpaceFunction.branch (fun c => decide (Allowed n W target c)) (allowed_fppred hn hW ht).flag_mem_FP R
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine E.congr (funext fun c => ?_)
  by_cases h : Allowed n W target c
  · simpa [h, value] using child_correct n W active target modulus c h
  · have hz := coefficient_eq_zero_of_not_allowed n W active target c h
    simp [h, value, hz, residueBits, BinaryNatCode.encode]

end LeanCanny.ETR.TubeZeroQuery
