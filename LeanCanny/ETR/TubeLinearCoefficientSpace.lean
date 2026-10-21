/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeMacaulayLayout
public import LeanCanny.ETR.IntegerResidueFP
public import LeanCanny.Algebra.LinearCoefficientSpace

/-! # Certified coefficients of the linear projection equation

The homogenizing coordinate has coefficient `X`; all other coordinates have
constant coefficients given by the negated integer direction. Only an FP
reader for encoded direction entries is supplied by the caller.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLinear
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.MatrixPower
open scoped BigOperators Classical

noncomputable def scalar (ell : List Bool → ℕ → ℤ) (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if i = 0 then Polynomial.X else -Polynomial.C (ell c i)

def scalarValue (ell degree modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  if BinaryNat.normalize (pairSnd q) = [] then
    if BinaryNat.normalize (degree (pairFst q)) = [true] then ArithmeticBits.one (BinaryNat.succ (modulus (pairFst q))) else []
  else if BinaryNat.normalize (degree (pairFst q)) = [] then
    ArithmeticBits.negate (pair (BinaryNat.succ (modulus (pairFst q)))
      (Codec.IntegerResidue.value (pair (ell q) (BinaryNat.succ (modulus (pairFst q))))))
  else []

theorem scalarValue_mem_FP {ell degree modulus : List Bool → List Bool}
    (he : ell ∈ FP) (hk : degree ∈ FP) (hm : modulus ∈ FP) : scalarValue ell degree modulus ∈ FP := by
  have hi := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have hdegree := mem_FP_comp (mem_FP_comp pairFst_mem_FP hk) BinaryNat.normalize_mem_FP
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) BinaryNat.succ_mem_FP
  have hone := mem_FP_comp hmod ArithmeticBits.one_mem_FP
  have hres := mem_FP_comp (mem_FP_pair he hmod) Codec.IntegerResidue.value_mem_FP
  have hneg := mem_FP_comp (mem_FP_pair hmod hres) ArithmeticBits.negate_mem_FP
  have h := (Brackets.stringEq_fppred hi (constFn_mem_FP [])).ite_mem_FP
    ((Brackets.stringEq_fppred hdegree (constFn_mem_FP [true])).ite_mem_FP
      hone (constFn_mem_FP []))
    ((Brackets.stringEq_fppred hdegree (constFn_mem_FP [])).ite_mem_FP hneg (constFn_mem_FP []))
  exact mem_FP_of_eq (g := scalarValue ell degree modulus) h (fun _ => by simp only [scalarValue, Function.comp_apply])

theorem scalarValue_packet (ell : List Bool → ℕ → ℤ) (read degree modulus : List Bool → List Bool)
    (c : List Bool) (i : ℕ) (he : read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits) :
    scalarValue read degree modulus (pair c (BinaryNatCode.encode i)) =
      RationalSubstitution.IntegerBits.coefficientResidue ((scalar ell c i).coeff (Nat.fromBitsLE (degree c)))
        (Nat.fromBitsLE (modulus c) + 1) := by
  let m := Nat.fromBitsLE (modulus c) + 1
  let : NeZero m := ⟨by dsimp only [m]; omega⟩
  have hm : BinaryNat.succ (modulus c) = BinaryNatCode.encode m := BinaryNat.succ_eq_bits _
  rw [scalarValue]
  simp only [pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode]
  change (if BinaryNatCode.encode i = [] then
    if BinaryNatCode.encode (Nat.fromBitsLE (degree c)) = [true] then ArithmeticBits.one (BinaryNat.succ (modulus c)) else []
    else if BinaryNatCode.encode (Nat.fromBitsLE (degree c)) = [] then
      ArithmeticBits.negate (pair (BinaryNat.succ (modulus c))
        (Codec.IntegerResidue.value (pair (read (pair c (BinaryNatCode.encode i))) (BinaryNat.succ (modulus c))))) else []) = _
  rw [hm]
  by_cases hi : i = 0
  · subst i
    rw [scalar, ite_eq_left rfl]
    by_cases hk : Nat.fromBitsLE (degree c) = 1
    · simp only [hk, show BinaryNatCode.encode 0 = [] from rfl, show BinaryNatCode.encode 1 = [true] from rfl,
        ite_true, Polynomial.coeff_X_one, RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_one]
      exact ArithmeticBits.one_residueBits m
    · have hn : BinaryNatCode.encode (Nat.fromBitsLE (degree c)) ≠ [true] := by
        change BinaryNatCode.encode _ ≠ BinaryNatCode.encode 1
        exact fun h => hk (BinaryNatCode.encode_injective h)
      simp only [show BinaryNatCode.encode 0 = [] from rfl, ite_true, hn, ite_false, Polynomial.coeff_X, Ne.symm hk,
        RationalSubstitution.IntegerBits.coefficientResidue]
      simp [residueBits, BinaryNatCode.encode]
  · have hin : BinaryNatCode.encode i ≠ [] := by
      change BinaryNatCode.encode i ≠ BinaryNatCode.encode 0
      exact fun h => hi (BinaryNatCode.encode_injective h)
    rw [ite_eq_right hin, scalar, ite_eq_right hi, Polynomial.coeff_neg]
    by_cases hk : Nat.fromBitsLE (degree c) = 0
    · rw [hk, show BinaryNatCode.encode 0 = [] from rfl, ite_eq_left rfl, Polynomial.coeff_C_zero, he,
        Codec.IntegerResidue.value_integer (ell c i) m, ArithmeticBits.negate_residueBits]
      simp only [RationalSubstitution.IntegerBits.coefficientResidue, Int.cast_neg]
    · have hn : BinaryNatCode.encode (Nat.fromBitsLE (degree c)) ≠ [] := by
        change BinaryNatCode.encode _ ≠ BinaryNatCode.encode 0
        exact fun h => hk (BinaryNatCode.encode_injective h)
      rw [ite_eq_right hn, Polynomial.coeff_C]
      simp [hk, RationalSubstitution.IntegerBits.coefficientResidue, residueBits, BinaryNatCode.encode]

noncomputable def polynomial (source : List Bool → List Bool) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    MvPolynomial (Fin (TubeParameter.spatialCount (source c))) (Polynomial ℤ) :=
  LinearCoefficientBits.polynomial (TubeParameter.spatialCount ∘ source) (scalar ell) c

theorem homogeneous (source : List Bool → List Bool) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    (polynomial source ell c).IsHomogeneous 1 := LinearCoefficientBits.homogeneous _ _ _

theorem eval_chart {K : Type*} [CommRing K] (source : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (φ : ℤ →+* K) (x : K)
    (z : Fin (TubeProjectionEncoding.pointCount (TubeIndexed.arity (source c)) + 1) → K) :
    (polynomial source ell c).eval₂ (Polynomial.eval₂RingHom φ x) (Fin.cases 1 z) =
      x - ∑ i, φ (ell c (i.val + 1)) * z i := by
  change (LinearCoefficientBits.polynomial
    (fun q => TubeProjectionEncoding.pointCount (TubeIndexed.arity (source q)) + 1 + 1) (scalar ell) c).eval₂
      (Polynomial.eval₂RingHom φ x) (Fin.cases 1 z) = _
  rw [LinearCoefficientBits.eval
    (fun q => TubeProjectionEncoding.pointCount (TubeIndexed.arity (source q)) + 1 + 1) (scalar ell) c
      (Polynomial.eval₂RingHom φ x) (Fin.cases 1 z)]
  change (∑ i : Fin (TubeProjectionEncoding.pointCount (TubeIndexed.arity (source c)) + 1 + 1),
    (Polynomial.eval₂RingHom φ x) (scalar ell c i.val) * Fin.cases 1 z i) = _
  rw [Fin.sum_univ_succ]
  simp only [scalar, Fin.val_zero, ite_true, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Fin.cases_zero, mul_one, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
    Polynomial.eval₂_neg, Polynomial.eval₂_C, Fin.cases_succ, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]

theorem matrixWidth_pos (bits : List Bool) : 0 < TubeCleared.matrixWidth bits := by
  have h := Nat.lt_size_self (TubeCleared.levelAllowance bits)
  have ha : 0 < TubeCleared.levelAllowance bits := by unfold TubeCleared.levelAllowance; omega
  by_contra hn
  have hz : TubeCleared.matrixWidth bits = 0 := by omega
  change (TubeCleared.levelAllowance bits).size = 0 at hz
  rw [hz] at h
  simp only [pow_zero] at h
  omega

theorem evaluator (source : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (read degree modulus : List Bool → List Bool) (hs : source ∈ FP) (he : read ∈ FP) (hk : degree ∈ FP) (hm : modulus ∈ FP)
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) →
      read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits) :
    SpaceFunction (LinearCoefficientBits.value (TubeParameter.spatialCount ∘ source) (TubeCleared.matrixWidth ∘ source)
      (scalar ell) degree modulus) :=
  LinearCoefficientBits.evaluator (TubeParameter.spatialCount_unary.comp hs) (TubeCleared.matrixWidth_unary.comp hs)
    (fun c => matrixWidth_pos (source c)) (scalar ell) degree modulus (scalarValue read degree modulus) hm
    (SpaceFunction.ofFP _ (scalarValue_mem_FP he hk hm)) (fun c i hi => scalarValue_packet ell read degree modulus c i (hr c i hi))

end LeanCanny.ETR.TubeLinear
