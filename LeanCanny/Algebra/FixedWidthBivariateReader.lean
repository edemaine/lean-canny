/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthKronecker
public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Computation.SpaceFunctionBranch
/-! # A native bivariate reader from streamed integer multivariate coefficients

All coefficient variables are packed into one Kronecker index; the outer
polynomial variable remains separate. Out-of-box indices return zero.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateReader
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
variable (A W : List Bool→ℕ)
variable (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ))

noncomputable def polynomial (c : List Bool) : (ℤ[X])[X] :=
  (p c).map (FixedWidthKronecker.encode (A c) (W c))

def origin (z : List Bool) :=pairFst (pairFst z)
def parameter (z : List Bool) :=Nat.fromBitsLE (pairFst (pairSnd z))
theorem origin_FP : origin∈FP :=by polytime [origin]
theorem parameter_binary : BinaryFn parameter :=
  BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

def valid (z : List Bool) : Prop :=parameter z<count (A (origin z)) (W (origin z))
instance (z : List Bool) : Decidable (valid A W z) :=inferInstanceAs (Decidable (_<_))

theorem valid_fppred (hA : UnaryFn A) (hW : UnaryFn W) : FPPred (valid A W) := by
  have HB : BinaryFn (fun c=>count (A c) (W c)) :=
    BinaryFn.of_bits (mem_FP_of_eq (countCode_mem_FP hA hW) (fun c=>countCode_code A W c))
  exact parameter_binary.lt (HB.comp origin_FP)

def value (coefficient : List Bool→List Bool) (z : List Bool) :=
  if valid A W z then coefficient z else []

theorem evaluator (coefficient : List Bool→List Bool) (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) : SpaceFunction (value A W coefficient) := by
  have HE:=SpaceFunction.branch (fun z=>decide (valid A W z)) (valid_fppred A W hA hW).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact HE.congr (funext fun z=>by simp only [value,decide_eq_true_eq])

theorem packet (coefficient : List Bool→List Bool) (D : List Bool→ℕ)
    (hP : ∀ c v,((p c).coeff v).totalDegree≤D c) (hW : ∀ c,D c<2^(W c))
    (hc : ∀ q u v,coefficient (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((p (pairFst q)).coeff v).coeff (nativeExponent (Equiv.refl _) (W (pairFst q)) u)) : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q)+1))) (q : List Bool) (u v : ℕ) :
    value A W coefficient (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits ((((polynomial A W p (pairFst q)).coeff v).coeff u : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1)) := by
  have HV : valid A W (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))↔
      u<count (A (pairFst q)) (W (pairFst q)) :=by
    simp only [valid,origin,parameter,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  simp only [value,polynomial,Polynomial.coeff_map]
  by_cases hu : u<count (A (pairFst q)) (W (pairFst q))
  · rw [ite_eq_left (HV.mpr hu),hc]
    have HC:=FixedWidthKronecker.native_coefficient (Equiv.refl _) (W (pairFst q)) (D (pairFst q))
      ((p (pairFst q)).coeff v) (hP _ v) (hW _) u hu
    have HE : (FixedWidthKronecker.encode (A (pairFst q)) (W (pairFst q))
        ((p (pairFst q)).coeff v)).coeff u=
        ((p (pairFst q)).coeff v).coeff (nativeExponent (Equiv.refl _) (W (pairFst q)) u) :=by
      simpa [FixedWidthKronecker.native] using HC
    rw [HE]
  · rw [ite_eq_right (fun h=>hu (HV.mp h))]
    have HF (e) (he : e∈((p (pairFst q)).coeff v).support) (i) : e i<2^W (pairFst q) :=
      ((MvPolynomial.monomial_le_degreeOf i he).trans
        ((MvPolynomial.degreeOf_le_totalDegree _ i).trans (hP _ v))).trans_lt (hW _)
    rw [FixedWidthKronecker.coefficient_of_ge _ _ _ HF u (by omega)]
    simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

noncomputable def reader (coefficient : List Bool→List Bool) (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (D : List Bool→ℕ)
    (hP : ∀ c v,((p c).coeff v).totalDegree≤D c) (hfit : ∀ c,D c<2^W c)
    (hc : ∀ q u v,coefficient (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((p (pairFst q)).coeff v).coeff (nativeExponent (Equiv.refl _) (W (pairFst q)) u)) : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q)+1))) : CertifiedPolynomial.BivariateReader (polynomial A W p) where
  coefficient:=value A W coefficient
  evaluator:=evaluator A W coefficient E hA hW
  coefficient_eq:=packet A W p coefficient D hP hfit hc

end LeanCanny.Algebra.FixedWidthBivariateReader
