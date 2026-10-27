/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.IteratedDerivativeSpace

/-! # Binary-indexed outer derivatives of bivariate coefficient readers

A streamed modular falling factorial multiplies one original coefficient.
The derivative order stays binary, and the independent parameter exponent
and the original positive modulus are retained.
-/

@[expose] public section
namespace LeanCanny.Algebra.CertifiedPolynomial.BivariateIteratedDerivative
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators

def source (z : List Bool) : List Bool := pairFst (pairFst z)
def index (z : List Bool) : List Bool := pairSnd (pairSnd z)
def modulus (z : List Bool) : List Bool := BinaryNat.succ (pairSnd (pairFst z))
def order (k : List Bool → List Bool) (z : List Bool) : List Bool := k (source z)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem index_FP : index ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
theorem order_FP {k : List Bool → List Bool} (hk : k ∈ FP) : order k ∈ FP := mem_FP_comp source_FP hk

def query (k : List Bool → List Bool) (z : List Bool) : List Bool := pair (pairFst z)
  (pair (BinaryNat.normalize (pairFst (pairSnd z))) (BinaryNat.add (pair (index z) (order k z))))
theorem query_FP {k : List Bool → List Bool} (hk : k ∈ FP) : query k ∈ FP := by
  have hi := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) BinaryNat.normalize_mem_FP
  have hv := mem_FP_comp (mem_FP_pair index_FP (order_FP hk)) BinaryNat.add_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair hi hv)

noncomputable def factorValue (k : List Bool → List Bool) (z : List Bool) : List Bool :=
  residueBits (((Nat.fromBitsLE (index z) + Nat.fromBitsLE (order k z)).descFactorial
    (Nat.fromBitsLE (order k z)) : ℕ) : ZMod (Nat.fromBitsLE (modulus z)))

theorem factor_evaluator {k : List Bool → List Bool} (hk : k ∈ FP) : SpaceFunction (factorValue k) := by
  have E := ModularProduct.evaluator
    (SpaceFunction.ofFP _ (IteratedDerivativeBits.factor_FP index_FP (order_FP hk) modulus_FP))
    (order k) modulus (order_FP hk) modulus_FP
    (fun z j => ((Nat.fromBitsLE (index z) + Nat.fromBitsLE (order k z) - j : ℕ) : ZMod (Nat.fromBitsLE (modulus z))))
    (fun z => by simp only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]; omega)
    (by
      intro z j _
      simp only [IteratedDerivativeBits.factor, pairFst_pair, pairSnd_pair, BinaryNat.mod_pair,
        BinaryNat.sub_pair, BinaryNat.add_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_natCast])
  refine E.congr (funext fun z => ?_)
  simp only [factorValue, Nat.descFactorial_eq_prod_range, Nat.cast_prod]

noncomputable def value {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p)
    (k : List Bool → List Bool) (z : List Bool) : List Bool :=
  IteratedDerivativeBits.finish modulus (pair z (pair (factorValue k z) (A.coefficient (query k z))))

theorem evaluator {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p)
    {k : List Bool → List Bool} (hk : k ∈ FP) : SpaceFunction (value A k) := by
  have E := ((factor_evaluator hk).pairOutputs (A.evaluator.precompose (query k) (query_FP hk))).withInput.postcompose
    (IteratedDerivativeBits.finish modulus) (IteratedDerivativeBits.finish_FP modulus_FP)
  exact E.congr (funext fun z => by simp only [value, Function.comp_apply])

private theorem raw_mul (m : ℕ) (a b : ZMod m) :
    BinaryNat.mulMod (pair (BinaryNatCode.encode m) (pair (residueBits a) (residueBits b))) = residueBits (a * b) := by
  simp only [BinaryNat.mulMod_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_mul]

theorem factor_packet (k : List Bool → List Bool) (q : List Bool) (u v : ℕ) :
    factorValue k (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) = residueBits
      (((v + Nat.fromBitsLE (k (pairFst q))).descFactorial (Nat.fromBitsLE (k (pairFst q))) : ℕ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  unfold factorValue
  exact congrArg₂ (fun (n m : ℕ) => residueBits (n : ZMod m))
    (by simp only [index, order, source, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
    (by simp only [modulus, pairFst_pair, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits])

theorem packet {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (k : List Bool → List Bool)
    (q : List Bool) (u v : ℕ) :
    value A k (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      residueBits (((((Polynomial.derivative^[Nat.fromBitsLE (k (pairFst q))]) (p (pairFst q))).coeff v).coeff u : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have hq : query k (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))) =
      pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode (v + Nat.fromBitsLE (k (pairFst q))))) := by
    simp only [query, index, order, source, pairFst_pair, pairSnd_pair, BinaryNat.normalize_bits,
      BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, hq, A.coefficient_eq, factor_packet]
  simp only [IteratedDerivativeBits.finish, modulus, pairFst_pair,
    pairSnd_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode]
  rw [show BinaryNat.mulMod (pair (Nat.fromBitsLE (pairSnd q) + 1).bits _ ) = _ from raw_mul _ _ _]
  simp only [Polynomial.coeff_iterate_derivative, nsmul_eq_mul, Polynomial.coeff_natCast_mul, Int.cast_mul, Int.cast_natCast]

noncomputable def reader {p : List Bool → (ℤ[X])[X]} (A : BivariateReader p)
    (k : List Bool → List Bool) (hk : k ∈ FP) :
    BivariateReader (fun c => (Polynomial.derivative^[Nat.fromBitsLE (k c)]) (p c)) where
  coefficient := value A k
  evaluator := evaluator A hk
  coefficient_eq := packet A k

end LeanCanny.Algebra.CertifiedPolynomial.BivariateIteratedDerivative
