/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.ModularNatMulFP

/-! # Native outer derivatives of bivariate integer coefficient readers

One original coefficient query increments the outer index. Modular
multiplication by that index supplies the derivative coefficient, retaining
the independent parameter index and the original modulus word.
-/

@[expose] public section
namespace LeanCanny.Algebra.CertifiedPolynomial.BivariateDerivative
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower

def query (z : List Bool) : List Bool := pair (pairFst z)
  (pair (BinaryNat.normalize (pairFst (pairSnd z))) (BinaryNat.succ (pairSnd (pairSnd z))))
theorem query_FP : query ∈ FP := by polytime [query]

def finish (t : List Bool) : List Bool := BinaryNat.mulMod
  (pair (BinaryNat.succ (pairSnd (pairFst (pairFst t))))
    (pair (pairSnd t) (BinaryNat.succ (pairSnd (pairSnd (pairFst t))))))
theorem finish_FP : finish ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have hi := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have H := mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hi)) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq H (fun t => by simp only [finish, Function.comp_apply])

def value {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (z : List Bool) : List Bool :=
  finish (pair z (A.coefficient (query z)))

theorem evaluator {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p) : SpaceFunction (value A) :=
  ((A.evaluator.precompose query query_FP).withInput.postcompose finish finish_FP).congr
    (funext fun z => by simp only [value, Function.comp_apply])

theorem packet {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (q : List Bool) (u v : ℕ) :
    value A (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits (((((p (pairFst q)).derivative).coeff v).coeff u : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have hq : query (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode (v + 1))) := by
    simp only [query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_bits, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, hq, A.coefficient_eq]
  simp only [finish, pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  refine (ArithmeticBits.mulMod_nat_residueBits (Nat.fromBitsLE (pairSnd q) + 1)
    ((((p (pairFst q)).coeff (v + 1)).coeff u : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) (v + 1)).trans ?_
  have hd : (((p (pairFst q)).derivative).coeff v).coeff u =
      ((p (pairFst q)).coeff (v + 1)).coeff u * ((v + 1 : ℕ) : ℤ) := by
    have H : ((p (pairFst q)).derivative).coeff v =
        (p (pairFst q)).coeff (v + 1) * ((v + 1 : ℕ) : ℤ[X]) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Polynomial.coeff_derivative (p (pairFst q)) v
    rw [H, Polynomial.coeff_mul_natCast]
  rw [hd, Int.cast_mul, Int.cast_natCast]

noncomputable def reader {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p) :
    BivariateReader (fun c => (p c).derivative) where
  coefficient := value A
  evaluator := evaluator A
  coefficient_eq := packet A

end LeanCanny.Algebra.CertifiedPolynomial.BivariateDerivative
