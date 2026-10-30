/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationPolynomialSpace

/-! # Native homogenization retaining polynomial coefficients

The coefficient parameter is carried unchanged through homogenization. A
binary spatial degree allowance, unary dimension and exponent width, and the
original coefficient reader suffice. No parameter specialization or actual
degree computation is introduced.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogenizationParameterBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open scoped Classical

noncomputable def source (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) (Polynomial ℤ))
    (parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits ((((p (pairFst q)).coeff (nativeExponent (Equiv.refl _) (W (pairFst q))
    (Nat.fromBitsLE (pairSnd q)))).coeff (Nat.fromBitsLE (parameter (pairFst q))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

noncomputable def polynomial (N D : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) (Polynomial ℤ)) (c : List Bool) :
    MvPolynomial (Fin (N c + 1)) (Polynomial ℤ) :=
  MvPolynomial.rename AffineCoordinateSystem.layout
    (WeightedHomogenization.homogenize (fun _ => 1) (D c) (p c))

noncomputable def value (N W D : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) (Polynomial ℤ))
    (parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits ((((polynomial N D p (pairFst q)).coeff
    (nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)))).coeff
      (Nat.fromBitsLE (parameter (pairFst q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

lemma source_packet (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) (Polynomial ℤ))
    (parameter modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    source N W p parameter modulus (pair c (BinaryNatCode.encode r)) =
      residueBits ((((p c).coeff (nativeExponent (Equiv.refl _) (W c) r)).coeff
        (Nat.fromBitsLE (parameter c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  rfl

lemma value_packet (N W D : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) (Polynomial ℤ))
    (parameter modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    value N W D p parameter modulus (pair c (BinaryNatCode.encode r)) =
      residueBits ((((polynomial N D p c).coeff (nativeExponent (Equiv.refl _) (W c) r)).coeff
        (Nat.fromBitsLE (parameter c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  rfl

theorem evaluator {N W D : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hD : BinaryFn D)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) (Polynomial ℤ))
    (parameter modulus : List Bool → List Bool) (E : SpaceFunction (source N W p parameter modulus)) :
    SpaceFunction (value N W D p parameter modulus) := by
  have EH := HomogenizationBits.evaluator_binary_degree hN hN hW hD E
  refine EH.congr (funext fun q => ?_)
  have hp := HomogenizationBits.value_packet N N W D (source N W p parameter modulus)
    (pairFst q) (Equiv.refl _) (p (pairFst q))
    (fun a : Polynomial ℤ => residueBits ((a.coeff (Nat.fromBitsLE (parameter (pairFst q))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by simp [residueBits, BinaryNatCode.encode])
    (fun r => source_packet N W p parameter modulus (pairFst q) r) (Nat.fromBitsLE (pairSnd q))
  have hn : HomogenizationBits.value N N W D (source N W p parameter modulus) q =
      HomogenizationBits.value N N W D (source N W p parameter modulus)
        (pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))) := by
    simp only [HomogenizationBits.value, HomogenizationBits.total, HomogenizationBits.oldQuery,
      rankTarget, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  rw [hn, hp]
  simp only [HomogenizationLayout.prefixWeight_all]
  unfold value polynomial
  rw [nativeExponent_refl, coeff_rename_rank]
  rfl

end LeanCanny.Algebra.HomogenizationParameterBits
