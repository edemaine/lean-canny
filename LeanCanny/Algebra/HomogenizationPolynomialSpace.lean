/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.HomogenizationBinarySpace
public import LeanCanny.Algebra.AffineCoordinateSystem
public import LeanCanny.Algebra.RationalSubstitutionResidue

/-! # Homogenized integer rows with a retained coefficient parameter

A native integer coefficient reader suffices. The retained parameter occurs
only in degree zero, and homogenization may use an exponentially large
binary degree allowance.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogenizationPolynomialBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial MatrixPower
open scoped Classical

noncomputable def integerValue (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (modulus : List Bool → List Bool)
    (q : List Bool) : List Bool :=
  residueBits (((p (pairFst q)).coeff (nativeExponent (Equiv.refl _) (W (pairFst q))
    (Nat.fromBitsLE (pairSnd q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

noncomputable def affineValue (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (parameter modulus : List Bool → List Bool)
    (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (parameter (pairFst q)) = 0 then integerValue N W p modulus q else []

theorem integer_packet (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (modulus : List Bool → List Bool)
    (c : List Bool) (r : ℕ) :
    integerValue N W p modulus (pair c (BinaryNatCode.encode r)) =
      residueBits (((p c).coeff (nativeExponent (Equiv.refl _) (W c) r) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  rfl

noncomputable def polynomial (N D : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (c : List Bool) :
    MvPolynomial (Fin (N c + 1)) (Polynomial ℤ) :=
  MvPolynomial.rename AffineCoordinateSystem.layout
    (WeightedHomogenization.homogenize (fun _ => 1) (D c) ((p c).map Polynomial.C))

noncomputable def value (N W D : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (parameter modulus : List Bool → List Bool)
    (q : List Bool) : List Bool :=
  residueBits ((((polynomial N D p (pairFst q)).coeff
    (nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)))).coeff
      (Nat.fromBitsLE (parameter (pairFst q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

theorem affine_packet (N W : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (parameter modulus : List Bool → List Bool)
    (c : List Bool) (r : ℕ) :
    affineValue N W p parameter modulus (pair c (BinaryNatCode.encode r)) =
      residueBits (((((p c).map Polynomial.C).coeff
        (nativeExponent (Equiv.refl _) (W c) r)).coeff (Nat.fromBitsLE (parameter c)) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  simp only [affineValue, integerValue, MvPolynomial.coeff_map, Polynomial.coeff_C]
  split_ifs <;> simp [residueBits, BinaryNatCode.encode]

theorem evaluator {N W D : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) (hD : BinaryFn D)
    (p : (c : List Bool) → MvPolynomial (Fin (N c)) ℤ) (parameter modulus : List Bool → List Bool)
    (hk : parameter ∈ FP) (E : SpaceFunction (integerValue N W p modulus)) :
    SpaceFunction (value N W D p parameter modulus) := by
  have hparam : BinaryFn (fun q => Nat.fromBitsLE (parameter (pairFst q))) :=
    (BinaryFn.fromBits hk).comp pairFst_mem_FP
  have hg := hparam.eq (BinaryFn.const 0)
  have EA : SpaceFunction (affineValue N W p parameter modulus) :=
    (SpaceFunction.branch _ hg.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun _ => by simp only [affineValue, decide_eq_true_eq])
  have EH := HomogenizationBits.evaluator_binary_degree hN hN hW hD EA
  refine EH.congr (funext fun q => ?_)
  have hp := HomogenizationBits.value_packet N N W D (affineValue N W p parameter modulus)
    (pairFst q) (Equiv.refl _) ((p (pairFst q)).map Polynomial.C)
    (fun a : Polynomial ℤ => residueBits ((a.coeff (Nat.fromBitsLE (parameter (pairFst q))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)))
    (by simp [residueBits, BinaryNatCode.encode])
    (fun r => affine_packet N W p parameter modulus (pairFst q) r) (Nat.fromBitsLE (pairSnd q))
  have hn : HomogenizationBits.value N N W D (affineValue N W p parameter modulus) q =
      HomogenizationBits.value N N W D (affineValue N W p parameter modulus)
        (pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))) := by
    simp only [HomogenizationBits.value, HomogenizationBits.total, HomogenizationBits.oldQuery,
      rankTarget, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  rw [hn, hp]
  simp only [HomogenizationLayout.prefixWeight_all]
  unfold value polynomial
  rw [nativeExponent_refl, coeff_rename_rank]
  rfl

end LeanCanny.Algebra.HomogenizationPolynomialBits
