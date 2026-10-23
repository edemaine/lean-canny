/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoercivePowerReaders
public import LeanCanny.Algebra.CoerciveQuerySystem
public import LeanCanny.Algebra.EmbeddedCoefficient
public import LeanCanny.Algebra.ModularResidueSpace
public import LeanCanny.Algebra.ImplicitPowerResidueFP

/-! # Native coefficient access for coercive sample queries -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveQueryReaders
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
attribute [local irreducible] CoercivePowerReaders.squareSource CoerciveSourceSampling.dimension
  CoercivePowerReaders.size CoercivePowerReaders.width

private noncomputable def residue (a : ℤ) (m : ℕ) : List Bool := residueBits (a : ZMod m)

private noncomputable def squareCoefficient (bits : List Bool) (W r : ℕ) : ℤ :=
  ((polynomial bits) ^ 2).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) W r)

noncomputable def squareDegree (input : List Bool → List Bool) (c : List Bool) : ℕ :=
  2 * degreeAllowance (input c) + 1

noncomputable def derivativeValue (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthDerivativeBits.value (dimension ∘ input) (CoercivePowerReaders.width ∘ input)
    (CoercivePowerReaders.width ∘ input) (squareDegree input) selected target (BinaryNat.succ ∘ modulus)
    (CoercivePowerReaders.value (input ∘ pairFst) pairSnd (modulus ∘ pairFst))

theorem derivativeEvaluator {input target modulus : List Bool → List Bool} {selected : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    SpaceFunction (derivativeValue input selected target modulus) :=
  FixedWidthDerivativeBits.evaluator _ _ _ _ _ _ _
    (CoercivePowerReaders.evaluator (mem_FP_comp pairFst_mem_FP hi) pairSnd_mem_FP
      (mem_FP_comp pairFst_mem_FP hm))
    (dimension_unary.comp hi) (CoercivePowerReaders.width_unary.comp hi)
    (CoercivePowerReaders.width_unary.comp hi)
    (((UnaryFn.const 2).mul (degreeAllowance_unary.comp hi)).add (UnaryFn.const 1))
    hs ht (mem_FP_comp hm BinaryNat.succ_mem_FP)

theorem derivative_value_eq (input target modulus : List Bool → List Bool) (selected : List Bool → ℕ)
    (c : List Bool) (i : Fin (dimension (input c))) (hs : selected c = i.val) :
    derivativeValue input selected target modulus c = residueBits
      (((MvPolynomial.pderiv i ((polynomial (input c)) ^ 2)).coeff
        (CoercivePowerReaders.exponent input target c) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have hdegree : ((polynomial (input c)) ^ 2).totalDegree ≤ squareDegree input c := by
    have hd := MvPolynomial.totalDegree_pow (polynomial (input c)) 2
    have hp := polynomial_degree (input c)
    unfold squareDegree
    omega
  have hcoef (r : ℕ) : CoercivePowerReaders.value (input ∘ pairFst) pairSnd (modulus ∘ pairFst)
      (pair c (BinaryNatCode.encode r)) = residueBits
      ((((polynomial (input c)) ^ 2).coeff (FixedWidthPolynomial.nativeExponent
        (Equiv.refl _) (CoercivePowerReaders.width (input c)) r) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
    have h := CoercivePowerReaders.value_eq (input ∘ pairFst) pairSnd (modulus ∘ pairFst)
      (pair c (BinaryNatCode.encode r))
    rw [CoercivePowerReaders.exponent_rank] at h
    change _ = residue (squareCoefficient ((input ∘ pairFst) (pair c (BinaryNatCode.encode r)))
      (CoercivePowerReaders.width ((input ∘ pairFst) (pair c (BinaryNatCode.encode r))))
      (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r))))) _ at h
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits] at h
    exact h
  exact FixedWidthDerivativeBits.packet _ _ _ _ _ _ _ (Equiv.refl _) _ c
    ((polynomial (input c)) ^ 2) i (Nat.fromBitsLE (modulus c) + 1) rfl hs (by unfold squareDegree; omega)
    hdegree (CoercivePowerReaders.squareDegree_lt (input c))
    (by simp only [Function.comp_apply, BinaryNat.succ_eq_bits]; rfl) hcoef

/-- Restrict a native query exponent to the point coordinates. -/
noncomputable def queryExponent (input target : List Bool → List Bool) (c : List Bool) :
    Fin (dimension (input c) + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i =>
    FixedWidthQuery.coordinate (CoercivePowerReaders.width ∘ input) target c i.val)

theorem queryExponent_rank (input target : List Bool → List Bool) (c : List Bool) :
    queryExponent input target c = FixedWidthPolynomial.nativeExponent
      (Equiv.refl (Fin (dimension (input c) + 1))) (CoercivePowerReaders.width (input c))
      (Nat.fromBitsLE (target c)) := by
  ext i
  simp only [queryExponent, FixedWidthPolynomial.nativeExponent, Finsupp.coe_equivFunOnFinite_symm,
    Function.comp_apply, Equiv.refl_apply, FixedWidthQuery.coordinate]
  rw [FixedWidthPolynomial.entry_eq_digit, BinaryNat.value_take, FixedWidthPolynomial.drop_value]

noncomputable def tailWord (input target : List Bool → List Bool) (c : List Bool) : List Bool :=
  (target c).drop (CoercivePowerReaders.width (input c))

theorem tailWord_FP {input target : List Bool → List Bool} (hi : input ∈ FP) (ht : target ∈ FP) :
    tailWord input target ∈ FP := drop_mem_FP ht (CoercivePowerReaders.width_unary.comp hi)

theorem exponent_tail (input target : List Bool → List Bool) (c : List Bool) :
    (queryExponent input target c).comapDomain Fin.succ (Fin.succ_injective _).injOn =
      CoercivePowerReaders.exponent input (tailWord input target) c := by
  ext i
  simp only [queryExponent, CoercivePowerReaders.exponent, Finsupp.comapDomain_apply,
    Finsupp.coe_equivFunOnFinite_symm, Fin.val_succ, FixedWidthQuery.coordinate,
    Function.comp_apply, tailWord, List.drop_drop]
  congr 3
  ring

private theorem coeff_rename_succ {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (e : Fin (n + 1) →₀ ℕ) :
    (MvPolynomial.rename Fin.succ p).coeff e =
      if e 0 = 0 then p.coeff (e.comapDomain Fin.succ (Fin.succ_injective _).injOn) else 0 := by
  classical
  rw [EmbeddedCoefficient.coeff_rename Fin.succ (Fin.succ_injective _) p e]
  simp only [EmbeddedCoefficient.value, Fin.range_succ,
    Set.subset_compl_singleton_iff, Finset.mem_coe, Finsupp.notMem_support_iff]

noncomputable def zeroParameter (input target : List Bool → List Bool) (c : List Bool) : Prop :=
  queryExponent input target c 0 = 0

theorem zeroParameter_fppred {input target : List Bool → List Bool} (hi : input ∈ FP) (ht : target ∈ FP) :
    FPPred (zeroParameter input target) := by
  have h := BinaryNat.le_fppred (take_mem_FP ht (CoercivePowerReaders.width_unary.comp hi)) (constFn_mem_FP [])
  apply h.of_iff
  intro c
  simp only [zeroParameter, queryExponent, Finsupp.coe_equivFunOnFinite_symm,
    FixedWidthQuery.coordinate, Fin.val_zero, zero_mul, List.drop_zero,
    Function.comp_apply, show Nat.fromBitsLE ([] : List Bool) = 0 from rfl, Nat.le_zero]

noncomputable def liftedSquareValue (input target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  if zeroParameter input target c then CoercivePowerReaders.value input (tailWord input target) modulus c else []

noncomputable def liftedDerivativeValue (input : List Bool → List Bool) (selected : List Bool → ℕ)
    (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  if zeroParameter input target c then derivativeValue input selected (tailWord input target) modulus c else []

theorem liftedSquareEvaluator {input target modulus : List Bool → List Bool}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (liftedSquareValue input target modulus) := by
  have h := SpaceFunction.branch (fun c => decide (zeroParameter input target c))
    (zeroParameter_fppred hi ht).flag_mem_FP
    (CoercivePowerReaders.evaluator hi (tailWord_FP hi ht) hm)
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact h.congr (funext fun c => by simp only [liftedSquareValue, decide_eq_true_eq])

theorem liftedDerivativeEvaluator {input target modulus : List Bool → List Bool} {selected : List Bool → ℕ}
    (hi : input ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) (hs : UnaryFn selected) :
    SpaceFunction (liftedDerivativeValue input selected target modulus) := by
  have h := SpaceFunction.branch (fun c => decide (zeroParameter input target c))
    (zeroParameter_fppred hi ht).flag_mem_FP
    (derivativeEvaluator hi (tailWord_FP hi ht) hm hs)
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact h.congr (funext fun c => by simp only [liftedDerivativeValue, decide_eq_true_eq])

theorem liftedSquare_value_eq (input target modulus : List Bool → List Bool) (c : List Bool) :
    liftedSquareValue input target modulus c = residueBits
      (((((CoerciveQuerySystem.lift (polynomial (input c))) ^ 2).coeff
        (queryExponent input target c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  rw [CoerciveQuerySystem.lift, ← map_pow, coeff_rename_succ, exponent_tail]
  by_cases hz : zeroParameter input target c
  · change queryExponent input target c 0 = 0 at hz
    simp only [liftedSquareValue, zeroParameter, hz, ite_true]
    exact CoercivePowerReaders.value_eq input (tailWord input target) modulus c
  · change queryExponent input target c 0 ≠ 0 at hz
    simp [liftedSquareValue, zeroParameter, hz, residueBits, BinaryNatCode.encode]

theorem liftedDerivative_value_eq (input target modulus : List Bool → List Bool) (selected : List Bool → ℕ)
    (c : List Bool) (i : Fin (dimension (input c))) (hs : selected c = i.val) :
    liftedDerivativeValue input selected target modulus c = residueBits
      ((((MvPolynomial.rename Fin.succ (MvPolynomial.pderiv i ((polynomial (input c)) ^ 2))).coeff
        (queryExponent input target c)) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  rw [coeff_rename_succ, exponent_tail]
  by_cases hz : zeroParameter input target c
  · change queryExponent input target c 0 = 0 at hz
    simp only [liftedDerivativeValue, zeroParameter, hz, ite_true]
    exact derivative_value_eq input (tailWord input target) modulus selected c i hs
  · change queryExponent input target c 0 ≠ 0 at hz
    simp [liftedDerivativeValue, zeroParameter, hz, residueBits, BinaryNatCode.encode]

end LeanCanny.ETR.CoerciveQueryReaders
