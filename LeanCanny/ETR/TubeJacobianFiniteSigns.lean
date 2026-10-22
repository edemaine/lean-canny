/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularJacobianReaders

/-! # A native finite-algebraic sign row for the actual regular Jacobian

The one streamed row is the actual integer determinant polynomial. Its sign
is prescribed without constructing its square or storing its coefficients.
-/

@[expose] public section
namespace LeanCanny.ETR.TubeJacobianFiniteSigns
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm
  TubeRegularJacobianBudget.polynomial TubeHomogenization.outputEquiv

variable (input active : List Bool → List Bool) (sgn : SignType)

theorem clearingWidth_le (bits : List Bool) :
    2 ^ TubeRegularJacobianBits.width bits ≤ 2 * TubeRegularJacobianBits.bound bits := by
  have hb : 0 < TubeRegularJacobianBits.bound bits := by
    have hd : 0 < TubeIndexed.degreeBound bits := by unfold TubeIndexed.degreeBound; omega
    exact hd.trans_le (le_max_right _ _)
  have hw : 0 < TubeRegularJacobianBits.width bits := Nat.size_pos.mpr hb
  have hh : 2 ^ (TubeRegularJacobianBits.width bits - 1) ≤ TubeRegularJacobianBits.bound bits := by
    by_contra h
    have hs := Nat.size_le.mpr (show TubeRegularJacobianBits.bound bits <
      2 ^ (TubeRegularJacobianBits.width bits - 1) by omega)
    change TubeRegularJacobianBits.width bits ≤ TubeRegularJacobianBits.width bits - 1 at hs
    omega
  calc
    _ = 2 * 2 ^ (TubeRegularJacobianBits.width bits - 1) := by
      calc
        _ = 2 ^ ((TubeRegularJacobianBits.width bits - 1) + 1) :=
          congrArg (fun k : ℕ => 2 ^ k) (by omega)
        _ = _ := by rw [pow_succ]; omega
    _ ≤ _ := Nat.mul_le_mul_left 2 hh

noncomputable def nativeCoefficient (bits act : List Bool) (r : ℕ) : ℤ :=
  (TubeRegularJacobianBudget.polynomial bits
    (activeSet (TubeIndexed.arity bits) act)).coeff
      (FixedWidthPolynomial.nativeExponent (TubeHomogenization.outputEquiv bits)
        (TubeRegularJacobianBits.width bits) r)

noncomputable def coefficient (c : List Bool) (_j r : ℕ) : ℤ :=
  nativeCoefficient (input c) (active c) r

noncomputable def source : FiniteLeafSignBits.Source (TubeRegularFiniteSigns.arity input) where
  count _ := 1
  terms c := FixedWidthPolynomial.count (TubeRegularFiniteSigns.arity input c)
    (TubeRegularJacobianBits.width (input c))
  degree c := TubeRegularJacobianBits.bound (input c)
  height c := TubeRegularJacobianBudget.massBudget (input c)
  coefficient := coefficient input active
  exponent c _ r i := FixedWidthPolynomial.entry (TubeRegularJacobianBits.width (input c)) r i
  pattern _ _ := sgn
  exponent_le c _ r _ i _ := (FixedWidthPolynomial.entry_lt (TubeRegularJacobianBits.width (input c)) r i).le.trans
    (clearingWidth_le (input c))
  coefficient_le c _j _r _ := TubeRegularJacobianBudget.coefficient_le (input c) _ _

theorem polynomial_eq (c : List Bool) (j : ℕ) :
    (source input active sgn).polynomial c j =
      MvPolynomial.rename (TubeHomogenization.outputEquiv (input c))
        (TubeRegularJacobianBudget.polynomial (input c)
          (activeSet (TubeIndexed.arity (input c)) (active c))) :=
  FixedWidthPolynomial.indexed_source_eq_rename _ _ _ _
    ((TubeRegularJacobianBudget.degree_le _ _).trans (le_max_left _ _))
    (TubeRegularJacobianBits.bound_lt _)

theorem eval_polynomial {R : Type*} [CommSemiring R] (c : List Bool) (j : ℕ)
    (phi : ℤ →+* R) (z : Fin (TubeRegularFiniteSigns.arity input c) → R) :
    ((source input active sgn).polynomial c j).eval₂ phi z =
      (TubeRegularJacobianBudget.polynomial (input c)
        (activeSet (TubeIndexed.arity (input c)) (active c))).eval₂ phi
          (fun i => z (TubeHomogenization.outputEquiv (input c) i)) := by
  rw [polynomial_eq]
  exact MvPolynomial.eval₂_rename _ _ _ _

/-- Discard the selected sign row and retain the original context. -/
def context (q : List Bool) : List Bool := pairFst (pairFst (pairFst q))

theorem context_FP : context ∈ FP :=
  (pairFst_mem_FP.comp pairFst_mem_FP).comp pairFst_mem_FP

noncomputable def value : List Bool → List Bool :=
  TubeRegularJacobianBits.value (input ∘ context) (active ∘ context) pairSnd (pairSnd ∘ pairFst)

theorem valueEvaluator (hi : input ∈ FP) (ha : active ∈ FP) :
    SpaceFunction (value input active) :=
  TubeRegularJacobianBits.evaluator _ _ _ _ (hi.comp context_FP) (ha.comp context_FP)
    pairSnd_mem_FP (pairSnd_mem_FP.comp pairFst_mem_FP)

private noncomputable def residue (a : ℤ) (m : ℕ) : List Bool :=
  MatrixPower.residueBits (a : ZMod m)

theorem value_packet (q : List Bool) (r m : ℕ)
    (hr : r < (source input active sgn).terms (pairFst q)) (hm : 0 < m) :
    value input active (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits ((coefficient input active (pairFst q)
        (Nat.fromBitsLE (pairSnd q)) r : ℤ) : ZMod m) := by
  have H := TubeRegularJacobianBits.value_packet (input ∘ context) (active ∘ context)
    pairSnd (pairSnd ∘ pairFst)
    (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) r
    (by simp only [Function.comp_apply, pairFst_pair, pairSnd_pair])
    (by simpa only [Function.comp_apply, context, pairFst_pair, source,
      TubeRegularFiniteSigns.arity, TubeRegularJacobianBits.arity] using hr)
  change value input active (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
    residue (nativeCoefficient
      ((input ∘ context) (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))))
      ((active ∘ context) (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1)))) r)
        (Nat.fromBitsLE (pairSnd
          (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1)))) + 1) at H
  simp only [Function.comp_apply, context, pairFst_pair, pairSnd_pair] at H
  exact H.trans (congrArg (residue (nativeCoefficient (input (pairFst q)) (active (pairFst q)) r))
    (by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]))

noncomputable def access (hi : input ∈ FP) (ha : active ∈ FP) : (source input active sgn).Access where
  coefficient := value input active
  exponent := FixedWidthPolynomial.exponentRead (TubeRegularFiniteSigns.arity input ∘ pairFst)
    ((TubeRegularJacobianBits.width ∘ input) ∘ pairFst)
  pattern _ := InfinitesimalSign.encode sgn
  count_unary := UnaryFn.const 1
  terms_binary := BinaryFn.of_bits (mem_FP_of_eq
    (FixedWidthPolynomial.countCode_mem_FP (TubeRegularFiniteSigns.arity_unary input hi)
      (TubeRegularJacobianBits.width_unary.comp hi)) (FixedWidthPolynomial.countCode_code _ _))
  degree_binary := BinaryFn.of_bits (bits_mem_FP (TubeRegularJacobianBits.bound_unary.comp hi))
  height_binary := BinaryFn.of_bits (bits_mem_FP (TubeRegularJacobianBudget.massBudget_unary.comp hi))
  coefficientEvaluator := valueEvaluator input active hi ha
  exponent_FP := FixedWidthPolynomial.exponentRead_mem_FP
    ((TubeRegularFiniteSigns.arity_unary input hi).comp pairFst_mem_FP)
    ((TubeRegularJacobianBits.width_unary.comp hi).comp pairFst_mem_FP)
  pattern_FP := constFn_mem_FP _
  coefficient_eq q r hr m hm := value_packet input active sgn q r m hr hm
  exponent_eq q r _ i hi := by
    rw [FixedWidthPolynomial.exponentRead_packet _ _ q r i hi]
    exact Nat.fromBitsLE_bits _
  pattern_eq _ _ := rfl

/-- The single native sign row is precisely the requested sign of the actual
regular Jacobian determinant. -/
theorem allSigns_iff (c : List Bool) (z : Fin (TubeRegularFiniteSigns.arity input c) → ℝ) :
    (∀ j : Fin ((source input active sgn).count c),
      SignType.sign (((source input active sgn).polynomial c j.val).eval₂ (Int.castRingHom ℝ) z) =
        (source input active sgn).pattern c j.val) ↔
      SignType.sign ((TubeRegularJacobianBudget.polynomial (input c)
        (activeSet (TubeIndexed.arity (input c)) (active c))).eval₂ (Int.castRingHom ℝ)
          (fun i => z (TubeHomogenization.outputEquiv (input c) i))) = sgn := by
  simp_rw [eval_polynomial]
  constructor
  · intro h
    exact h ⟨0, by simp [source]⟩
  · intro h _
    exact h

end LeanCanny.ETR.TubeJacobianFiniteSigns
