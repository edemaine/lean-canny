/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSparseReaders

/-! # Native residues for all actual coercive sampling rows

The original compiled square, its derivatives, the sparse diagonal penalty,
and the implicit large power of two are computed internally. Input, exponent
word, selected coordinate, and positive modulus predecessor are native FP fields.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveQueryCoefficient
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveQueryReaders CoerciveSparseReaders
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width

def addValue (modulus f g : List Bool → List Bool) (c : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (BinaryNat.succ (modulus c)) (pair (f c) (g c)))
def negValue (modulus f : List Bool → List Bool) (c : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNat.succ (modulus c)) (f c))

private theorem addEvaluator {modulus f g : List Bool → List Bool} (hm : modulus ∈ FP)
    (F : SpaceFunction f) (G : SpaceFunction g) : SpaceFunction (addValue modulus f g) := by
  have hfinish := mem_FP_comp (ModularResidueSpace.prepare_mem_FP modulus hm) ArithmeticBits.addMod_mem_FP
  have E := (F.pairOutputs G).withInput.postcompose _ hfinish
  exact E.congr (funext fun c => by simp only [Function.comp_apply, ModularResidueSpace.prepare,
    pairFst_pair, pairSnd_pair, addValue])

private theorem negEvaluator {modulus f : List Bool → List Bool} (hm : modulus ∈ FP)
    (F : SpaceFunction f) : SpaceFunction (negValue modulus f) := by
  have hfinish := mem_FP_comp (ModularResidueSpace.prepare_mem_FP modulus hm) ArithmeticBits.negate_mem_FP
  have E := F.withInput.postcompose _ hfinish
  exact E.congr (funext fun c => by simp only [Function.comp_apply, ModularResidueSpace.prepare,
    pairFst_pair, pairSnd_pair, negValue])

noncomputable def implicitValue (input modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  residueBits (((2 : ℤ) ^ CoerciveSourceSampling.penaltyExponent (input c) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus c) + 1))

theorem implicitValue_FP {input modulus : List Bool → List Bool} (hi : input ∈ FP) (hm : modulus ∈ FP) :
    implicitValue input modulus ∈ FP := by
  have h := ImplicitPowerResidue.power_two_mem_FP (CoerciveSourceControls.penaltyCode ∘ input) modulus
    (mem_FP_comp hi CoerciveSourceControls.penaltyCode_mem_FP) hm
  exact mem_FP_of_eq h (fun c => by simp only [Function.comp_apply,
    CoerciveSourceControls.penaltyCode_value, implicitValue])

noncomputable def maskedPowerValue (input target modulus : List Bool → List Bool)
    (parameter : List Bool → ℕ) (c : List Bool) : List Bool :=
  if Matches input target parameter (fun _ => 0) (fun _ => 0) c then implicitValue input modulus c else []

theorem maskedPowerEvaluator {input target modulus : List Bool → List Bool} {parameter : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) (hp : UnaryFn parameter) :
    SpaceFunction (maskedPowerValue input target modulus parameter) := by
  have hmatch := matches_fppred hi ht hp (UnaryFn.const 0) (UnaryFn.const 0)
  have E := SpaceFunction.branch (fun c => decide (Matches input target parameter (fun _ => 0) (fun _ => 0) c))
    hmatch.flag_mem_FP (SpaceFunction.ofFP _ (implicitValue_FP hi hm))
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact E.congr (funext fun c => by simp only [maskedPowerValue, decide_eq_true_eq])

theorem maskedPower_value_eq (input target modulus : List Bool → List Bool)
    (parameter : List Bool → ℕ) (c : List Bool) : maskedPowerValue input target modulus parameter c = residueBits
      (((MvPolynomial.monomial (Finsupp.single (0 : Fin (dimension (input c) + 1)) (parameter c))
        ((2 : ℤ) ^ CoerciveSourceSampling.penaltyExponent (input c))).coeff (queryExponent input target c) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  rw [MvPolynomial.coeff_monomial]
  unfold maskedPowerValue
  rw [matches_parameter_iff]
  by_cases h : queryExponent input target c = Finsupp.single 0 (parameter c)
  · simp only [h, ite_true, implicitValue]
  · simp [h, eq_comm, residueBits, BinaryNatCode.encode]

noncomputable def pureGradientValue (input target modulus : List Bool → List Bool) (selected : List Bool → ℕ) :
    List Bool → List Bool := monomialValue input target modulus (fun _ => 1)
      (fun c => 2 * degreeAllowance (input c) + 1) selected (fun c => 2 * degreeAllowance (input c) + 2)

theorem pureGradientValue_FP {input target modulus : List Bool → List Bool} {selected : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    pureGradientValue input target modulus selected ∈ FP :=
  monomialValue_FP hi ht hm (UnaryFn.const 1)
    (((UnaryFn.const 2).mul (degreeAllowance_unary.comp hi)).add (UnaryFn.const 1)) hs
    (((UnaryFn.const 2).mul (degreeAllowance_unary.comp hi)).add (UnaryFn.const 2))

noncomputable def gradientValue (input target modulus : List Bool → List Bool) (selected : List Bool → ℕ) :
    List Bool → List Bool := addValue modulus (liftedDerivativeValue input selected target modulus)
      (pureGradientValue input target modulus selected)
noncomputable def boundValue (input target modulus : List Bool → List Bool) : List Bool → List Bool :=
  addValue modulus (penaltyValue input target modulus) (negValue modulus (maskedPowerValue input target modulus (fun _ => 0)))
noncomputable def residualValue (input target modulus : List Bool → List Bool) : List Bool → List Bool :=
  addValue modulus (liftedSquareValue input target modulus) (negValue modulus (maskedPowerValue input target modulus (fun _ => 1)))

theorem gradientEvaluator {input target modulus : List Bool → List Bool} {selected : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    SpaceFunction (gradientValue input target modulus selected) :=
  addEvaluator hm (liftedDerivativeEvaluator hi ht hm hs) (SpaceFunction.ofFP _ (pureGradientValue_FP hi ht hm hs))

theorem boundEvaluator {input target modulus : List Bool → List Bool}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (boundValue input target modulus) :=
  addEvaluator hm (SpaceFunction.ofFP _ (penaltyValue_FP hi ht hm))
    (negEvaluator hm (maskedPowerEvaluator hi ht hm (UnaryFn.const 0)))

theorem residualEvaluator {input target modulus : List Bool → List Bool}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (residualValue input target modulus) :=
  addEvaluator hm (liftedSquareEvaluator hi ht hm)
    (negEvaluator hm (maskedPowerEvaluator hi ht hm (UnaryFn.const 1)))

private theorem pureGradient_eq {n : ℕ} (D : ℕ) (i : Fin n) :
    (MvPolynomial.C ((2 * D + 2 : ℕ) : ℤ) * MvPolynomial.X 0 * MvPolynomial.X i.succ ^ (2 * D + 1) :
      MvPolynomial (Fin (n + 1)) ℤ) =
      MvPolynomial.monomial (Finsupp.single 0 1 + Finsupp.single i.succ (2 * D + 1)) ((2 * D + 2 : ℕ) : ℤ) := by
  change MvPolynomial.C _ * MvPolynomial.monomial (Finsupp.single 0 1) 1 * _ = _
  rw [MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial, mul_one]

private theorem parameterPower_eq {n : ℕ} (E : ℕ) :
    (MvPolynomial.X 0 * MvPolynomial.C ((2 : ℤ) ^ E) : MvPolynomial (Fin (n + 1)) ℤ) =
      MvPolynomial.monomial (Finsupp.single 0 1) ((2 : ℤ) ^ E) := by
  rw [mul_comm, show (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) ℤ) =
    MvPolynomial.monomial (Finsupp.single 0 1) 1 from rfl, MvPolynomial.C_mul_monomial, mul_one]

theorem gradient_value_eq (input target modulus : List Bool → List Bool) (selected : List Bool → ℕ)
    (c : List Bool) (i : Fin (dimension (input c))) (hs : selected c = i.val) :
    gradientValue input target modulus selected c = residueBits
      (((CoerciveQuerySystem.gradient (polynomial (input c)) (degreeAllowance (input c)) i).coeff
        (queryExponent input target c) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let m := Nat.fromBitsLE (modulus c) + 1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  have hword : BinaryNat.succ (modulus c) = BinaryNatCode.encode m := by rw [BinaryNat.succ_eq_bits]; rfl
  rw [gradientValue, addValue, liftedDerivative_value_eq input target modulus selected c i hs,
    pureGradientValue, monomial_value_eq input target modulus _ _ _ _ c i hs, hword,
    ArithmeticBits.addMod_residueBits]
  simp only [CoerciveQuerySystem.gradient, pureGradient_eq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Int.cast_add]

theorem bound_value_eq (input target modulus : List Bool → List Bool) (c : List Bool) :
    boundValue input target modulus c = residueBits
      (((CoerciveQuerySystem.bound (n := dimension (input c)) (degreeAllowance (input c))
        (CoerciveSourceSampling.penaltyExponent (input c))).coeff (queryExponent input target c) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let m := Nat.fromBitsLE (modulus c) + 1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  have hword : BinaryNat.succ (modulus c) = BinaryNatCode.encode m := by rw [BinaryNat.succ_eq_bits]; rfl
  rw [boundValue, addValue, negValue, penalty_value_eq, maskedPower_value_eq, hword,
    ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  simp only [CoerciveQuerySystem.bound, Finsupp.single_zero, MvPolynomial.monomial_zero',
    AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Int.cast_sub]
  rw [sub_eq_add_neg]

theorem residual_value_eq (input target modulus : List Bool → List Bool) (c : List Bool) :
    residualValue input target modulus c = residueBits
      (((CoerciveQuerySystem.residual (polynomial (input c))
        (CoerciveSourceSampling.penaltyExponent (input c))).coeff (queryExponent input target c) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let m := Nat.fromBitsLE (modulus c) + 1
  let : NeZero m := ⟨by dsimp [m]; omega⟩
  have hword : BinaryNat.succ (modulus c) = BinaryNatCode.encode m := by rw [BinaryNat.succ_eq_bits]; rfl
  rw [residualValue, addValue, negValue, liftedSquare_value_eq, maskedPower_value_eq, hword,
    ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  simp only [CoerciveQuerySystem.residual, parameterPower_eq, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, Int.cast_sub]
  rw [sub_eq_add_neg]

end LeanCanny.ETR.CoerciveQueryCoefficient
