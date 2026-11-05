/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.EvenPolynomialCharacteristicSpace
public import LeanCanny.Algebra.PaddedCharacteristicFactorSpace
public import LeanCanny.Algebra.SymbolicScaledQuotientSpace
public import LeanCanny.Algebra.BivariateReaderCanonical
/-! # Native monic padded characteristic quotients

The two matrices use the same even full-box dimension. Their original entry
coefficient routines are charged, as are the binary padding exponent and the
retained-parameter degree bound. This is a backend interface; the concrete
Macaulay and original-source bindings are separate obligations.
-/
@[expose] public section
namespace LeanCanny.Algebra.PaddedCharacteristicQuotientBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def family (N r : List Bool → ℕ)
    (A E : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ)) :
    SymbolicScaledQuotientBits.Family where
  divisor c := (E c).charpoly
  dividend c := (A c).charpoly * (1 - X) ^ r c
  divisorDegree := N
  quotientDegree := r

theorem padding_coefficient_degree (r k : ℕ) :
    (((1 - X : Polynomial (Polynomial ℤ)) ^ r).coeff k).natDegree ≤ 0 := by
  have HM : (1 - X : Polynomial (Polynomial ℤ)) ^ r =
      ((1 - X : Polynomial ℤ) ^ r).map Polynomial.C := by simp
  rw [HM, coeff_map]
  exact le_of_eq (natDegree_C _)

theorem dividend_coefficient_degree (N r B : List Bool → ℕ)
    (A : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (hA : ∀ c i j, (A c i j).natDegree ≤ B c) (c : List Bool) (k : ℕ) :
    (((A c).charpoly * (1 - X) ^ r c).coeff k).natDegree ≤ N c * B c := by
  apply (PolynomialKronecker.inner_degree_iff_swap _ _).mpr ?_ k
  rw [map_mul]
  have HA := (PolynomialKronecker.inner_degree_iff_swap _ _).mp
    (EvenPolynomialCharacteristicBits.coefficient_degree N B A hA c)
  have HP := (PolynomialKronecker.inner_degree_iff_swap _ _).mp
    (padding_coefficient_degree (r c))
  exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add HA HP).trans_eq (Nat.add_zero _))

theorem evaluator (N r B : List Bool → ℕ)
    (A E : (c : List Bool) → Matrix (Fin (N c)) (Fin (N c)) (Polynomial ℤ))
    (hN : ∀ c, 0 < N c) (hEven : ∀ c, Even (N c))
    (hn : BinaryFn N) (hr : BinaryFn r) (hB : BinaryFn B)
    (hA : ∀ c i j, (A c i j).natDegree ≤ B c)
    (hE : ∀ c i j, (E c i j).natDegree ≤ B c)
    (sourceA sourceE : List Bool → List Bool)
    (SA : SpaceFunction sourceA) (SE : SpaceFunction sourceE)
    (hcA : ∀ c m (i j : Fin (N c)) u,
      sourceA (pair (pair c m) (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
          residueBits ((((A c i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE m + 1)))
    (hcE : ∀ c m (i j : Fin (N c)) u,
      sourceE (pair (pair c m) (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode u)))) =
          residueBits ((((E c i j).coeff u) : ℤ) : ZMod (Nat.fromBitsLE m + 1))) :
    SpaceFunction (family N r A E).value := by
  let RA := EvenPolynomialCharacteristicBits.reader N B A hN hEven hn hB hA sourceA SA hcA
  let RE := EvenPolynomialCharacteristicBits.reader N B E hN hEven hn hB hE sourceE SE hcE
  let RP := CertifiedPolynomial.BivariateProduct.reader RA (PaddedCharacteristicFactorBits.reader r hr)
  exact (family N r A E).evaluator (fun c => N c * B c)
    (EvenPolynomialCharacteristicBits.coefficient_degree N B E hE)
    (dividend_coefficient_degree N r B A hA) hn hr (hn.mul hB)
    (BivariateReaderCanonical.evaluator RE) (BivariateReaderCanonical.evaluator RP)

end LeanCanny.Algebra.PaddedCharacteristicQuotientBits
