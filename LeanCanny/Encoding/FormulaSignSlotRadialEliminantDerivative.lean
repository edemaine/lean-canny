/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialFormalInput
public import LeanCanny.Algebra.IntegralOriginalTermCoefficientSpace
public import LeanCanny.Algebra.FixedWidthDerivativeCoefficientSpace
/-! # Original-only coefficients of the dense tilted-system derivative term

There is one streamed coefficient call to the actual squared formal input.
Neither a derivative syntax tree nor an externally supplied reader is needed.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantDerivative
open ETR LeanCanny.Algebra LeanCanny.Computation MatrixPower
open LeanCanny.Connectivity FormulaSignSlotCenteredRadialLimits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalInput.polynomial FormulaSignSlotRadialFormalInput.equation

noncomputable def source (read : List Bool → List Bool) (c : List Bool) :=
  ((FormulaSignSlotRadialFormalInput.equation (read c)).square).toData.toBits

theorem source_FP {read : List Bool → List Bool} (hr : read ∈ FP) : source read ∈ FP := by
  have H := mem_FP_comp hr FormulaSignSlotRadialFormalInput.equation_FP
  apply mem_FP_of_eq (Codec.taggedTwo_mem_FP 3 H H)
  intro c
  simp only [source, Term.square, Term.mul_toBits, Function.comp_apply]

noncomputable def degree (read : List Bool → List Bool) (c : List Bool) := 2 * degreeBudget (read c) + 1
noncomputable def width (read : List Bool → List Bool) (c : List Bool) := degree read c + 1

theorem degree_unary {read : List Bool → List Bool} (hr : read ∈ FP) : UnaryFn (degree read) :=
  ((UnaryFn.const 2).mul (degreeBudget_unary.comp hr)).add (UnaryFn.const 1)
theorem width_unary {read : List Bool → List Bool} (hr : read ∈ FP) : UnaryFn (width read) :=
  (degree_unary hr).add (UnaryFn.const 1)

private theorem from_source (A W V D selected : List Bool → ℕ)
    (p : (c : List Bool) → MvPolynomial (Fin (A c)) ℤ)
    (word target modulus : List Bool → List Bool)
    (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : BinaryFn D)
    (hs : UnaryFn selected) (hselected : ∀ c, selected c < A c)
    (hpos : ∀ c, 0 < D c) (hp : ∀ c, (p c).totalDegree ≤ D c)
    (hw : ∀ c, D c < 2 ^ W c) (hword : word ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (ha : ∀ c, (TermView.term (word c)).arity ≤ A c)
    (he : ∀ c, (TermView.term (word c)).finitePolynomial (A c) = p c) :
    SpaceFunction (FixedWidthRowBits.value A V
      (fun c => MvPolynomial.pderiv ⟨selected c, hselected c⟩ (p c)) target modulus) := by
  have E := IntegralOriginalTermCoefficientBits.evaluator A W
    (fun c => Nat.fromBitsLE (modulus c) + 1) hA hW
    ((BinaryFn.fromBits hm).add (BinaryFn.const 1)) (fun _ => Nat.succ_ne_zero _) p word hword ha he
  apply FixedWidthDerivativeBits.coefficient_evaluator A W V D selected target modulus
    (IntegralOriginalTermCoefficientBits.scalar A W (fun c => Nat.fromBitsLE (modulus c) + 1) p)
    p hselected hpos hp hw hA hW hV hD hs ht hm E
  intro c r
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  subst r
  unfold IntegralOriginalTermCoefficientBits.scalar
  apply congrArg (fun e => residueBits ((p (pairFst z)).coeff e : ZMod (Nat.fromBitsLE (modulus (pairFst z)) + 1)))
  ext i
  rfl

theorem evaluator (read : List Bool → List Bool) (hr : read ∈ FP)
    (V selected : List Bool → ℕ) (hV : UnaryFn V) (hs : UnaryFn selected)
    (hselected : ∀ c, selected c < FormulaSignSlotRadialFormalInput.dimension (read c))
    (target modulus : List Bool → List Bool) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (FixedWidthRowBits.value (FormulaSignSlotRadialFormalInput.dimension ∘ read) V
      (fun c => MvPolynomial.pderiv ⟨selected c, hselected c⟩
        ((FormulaSignSlotRadialFormalInput.polynomial (read c)) ^ 2)) target modulus) := by
  have HP : ∀ c, ((FormulaSignSlotRadialFormalInput.polynomial (read c)) ^ 2).totalDegree ≤ degree read c := by
    intro c
    exact (MvPolynomial.totalDegree_pow _ 2).trans
      ((Nat.mul_le_mul_left 2 (FormulaSignSlotRadialFormalInput.polynomial_degree (read c))).trans
        (Nat.le_succ _))
  have HA : ∀ c, (TermView.term (source read c)).arity ≤ FormulaSignSlotRadialFormalInput.dimension (read c) := by
    intro c
    rw [source, TermView.term_toBits]
    simpa only [Term.square, Term.arity, max_self] using FormulaSignSlotRadialFormalInput.scope (read c)
  have HE : ∀ c, (TermView.term (source read c)).finitePolynomial
      (FormulaSignSlotRadialFormalInput.dimension (read c)) = (FormulaSignSlotRadialFormalInput.polynomial (read c)) ^ 2 := by
    intro c
    rw [source, TermView.term_toBits]
    change (FormulaSignSlotRadialFormalInput.equation (read c)).finitePolynomial
      (FormulaSignSlotRadialFormalInput.dimension (read c)) *
      (FormulaSignSlotRadialFormalInput.equation (read c)).finitePolynomial
        (FormulaSignSlotRadialFormalInput.dimension (read c)) = _
    rw [FormulaSignSlotRadialFormalInput.finitePolynomial_eq]
    exact (pow_two _).symm
  exact from_source (FormulaSignSlotRadialFormalInput.dimension ∘ read) (width read) V (degree read)
    selected (fun c => (FormulaSignSlotRadialFormalInput.polynomial (read c)) ^ 2)
    (source read) target modulus (FormulaSignSlotRadialFormalInput.dimension_unary.comp hr)
    (width_unary hr) hV (BinaryFn.ofUnary (degree_unary hr)) hs hselected
    (fun _ => by unfold degree; omega) HP (fun _ => Nat.lt_trans (Nat.lt_succ_self _) Nat.lt_two_pow_self)
    (source_FP hr) ht hm HA HE

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantDerivative
