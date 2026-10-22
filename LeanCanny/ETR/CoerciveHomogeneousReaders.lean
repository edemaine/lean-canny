/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveQueryCoefficient
public import LeanCanny.Algebra.CoerciveHomogeneousCoefficient
public import LeanCanny.Algebra.HomogenizationSpace

/-! # Native bivariate coefficients of coercive homogeneous rows -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveHomogeneousReaders
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveQueryReaders
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

noncomputable def residue (a : ℤ) (m : ℕ) : List Bool := residueBits (a : ZMod m)

noncomputable def derivativeCoefficient (bits : List Bool) (i W r : ℕ) : ℤ :=
  if hi : i < dimension bits then
    (MvPolynomial.pderiv ⟨i, hi⟩ ((polynomial bits) ^ 2)).coeff
      (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W r) else 0

noncomputable def derivativeReader (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residue (derivativeCoefficient (input (pairFst q)) (selected (pairFst q))
    (CoercivePowerReaders.width (input (pairFst q))) (Nat.fromBitsLE (pairSnd q)))
      (Nat.fromBitsLE (modulus (pairFst q)) + 1)

theorem derivativeReaderEvaluator {input modulus : List Bool → List Bool} {selected : List Bool → ℕ}
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    SpaceFunction (derivativeReader input selected modulus) := by
  let guard : List Bool → Prop := fun q => selected (pairFst q) < dimension (input (pairFst q))
  have hg : FPPred guard := FPPred.lt hs.lift ((dimension_unary.comp hi).lift)
  have E := derivativeEvaluator (mem_FP_comp pairFst_mem_FP hi) pairSnd_mem_FP
    (mem_FP_comp pairFst_mem_FP hm) hs.lift
  have EB := SpaceFunction.branch (fun q => decide (guard q)) hg.flag_mem_FP E
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine EB.congr (funext fun q => ?_)
  by_cases hv : selected (pairFst q) < dimension (input (pairFst q))
  · simp only [guard, hv, decide_true, ite_true]
    change derivativeValue (input ∘ pairFst) (selected ∘ pairFst) pairSnd (modulus ∘ pairFst) q = _
    rw [derivative_value_eq (input ∘ pairFst) pairSnd (modulus ∘ pairFst) (selected ∘ pairFst)
      q ⟨selected (pairFst q), hv⟩ rfl, CoercivePowerReaders.exponent_rank]
    simp only [derivativeReader, residue, derivativeCoefficient, hv, dite_eq_left, Function.comp_apply]
  · simp only [guard, hv, decide_false, Bool.false_eq_true, ite_false,
      derivativeReader, residue, derivativeCoefficient]
    simp only [residueBits, BinaryNatCode.encode]
    rfl

theorem derivativeReader_packet (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    derivativeReader input selected modulus (pair c (BinaryNatCode.encode r)) =
      residueBits ((derivativeCoefficient (input c) (selected c) (CoercivePowerReaders.width (input c)) r : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  simp only [derivativeReader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def ordinaryValue (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) : List Bool → List Bool :=
  HomogenizationBits.value (dimension ∘ input) (dimension ∘ input) (CoercivePowerReaders.width ∘ input)
    (fun c => 2 * degreeAllowance (input c) + 1) (derivativeReader input selected modulus)

theorem ordinaryEvaluator {input modulus : List Bool → List Bool} {selected : List Bool → ℕ}
    (hi : input ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    SpaceFunction (ordinaryValue input selected modulus) :=
  HomogenizationBits.evaluator (dimension_unary.comp hi) (dimension_unary.comp hi)
    (CoercivePowerReaders.width_unary.comp hi)
    (((UnaryFn.const 2).mul (degreeAllowance_unary.comp hi)).add (UnaryFn.const 1))
    (derivativeReaderEvaluator hi hm hs)

theorem ordinary_packet (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (modulus : List Bool → List Bool) (c : List Bool) (i : Fin (dimension (input c)))
    (hs : selected c = i.val) (r : ℕ) :
    ordinaryValue input selected modulus (pair c (BinaryNatCode.encode r)) = residueBits
      (((WeightedHomogenization.homogenize (fun _ => 1) (2 * degreeAllowance (input c) + 1)
        (MvPolynomial.pderiv i ((polynomial (input c)) ^ 2))).coeff
        (FixedWidthPolynomial.nativeExponent (CoerciveCriticalHomogenization.layout)
          (CoercivePowerReaders.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have hp (k : ℕ) : derivativeReader input selected modulus (pair c (BinaryNatCode.encode k)) =
      residueBits (((MvPolynomial.pderiv i ((polynomial (input c)) ^ 2)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (CoercivePowerReaders.width (input c)) k) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
    rw [derivativeReader_packet, hs, derivativeCoefficient, dite_eq_left i.isLt]
  have h := HomogenizationBits.value_packet (dimension ∘ input) (dimension ∘ input)
    (CoercivePowerReaders.width ∘ input) (fun c => 2 * degreeAllowance (input c) + 1)
    (derivativeReader input selected modulus) c (Equiv.refl _)
    (MvPolynomial.pderiv i ((polynomial (input c)) ^ 2))
    (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (by simp [residueBits, BinaryNatCode.encode]) hp r
  have hw (N : ℕ) : HomogenizationLayout.prefixWeight (Equiv.refl (Fin N)) N =
      (fun _ => 1) := by funext j; simp [HomogenizationLayout.prefixWeight]
  have he := congrArg (fun w : Fin (dimension (input c)) → ℕ =>
    WeightedHomogenization.homogenize w (2 * degreeAllowance (input c) + 1)
      (MvPolynomial.pderiv i ((polynomial (input c)) ^ 2))) (hw (dimension (input c)))
  exact h.trans (congrArg (fun p : MvPolynomial (Option (Fin (dimension (input c)))) ℤ =>
    residueBits ((p.coeff (FixedWidthPolynomial.nativeExponent CoerciveCriticalHomogenization.layout
      (CoercivePowerReaders.width (input c)) r) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) he)

end LeanCanny.ETR.CoerciveHomogeneousReaders
