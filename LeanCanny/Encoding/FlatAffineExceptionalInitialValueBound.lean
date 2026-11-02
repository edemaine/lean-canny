/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalParentBank
public import LeanCanny.Algebra.IntegerRootBound

/-! # Original-source bounds for the initial exceptional parent values

The actual coordinate and exceptional roots satisfy their original integer
polynomials. Their coefficient mass gives a real root bound before any new
level coefficient or later mixed critical birth is introduced. Common clearing
retains exactly these values under the correlated old parent hom.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalInitialValueBound
open LeanCanny.Algebra
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births finitePolynomial finite_nonzero massBound)

noncomputable def height (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : ℕ := massBound F C h u+1

theorem height_binary {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (hh : UnaryFn (fun u => (h u).val)) : BinaryFn (height F C h) :=
  (FlatAffineExceptionalBankSource.massBound_binary hF C h hh).add (BinaryFn.const 1)

attribute [local irreducible] FlatAffineExceptionalParentBank.values finitePolynomial massBound

theorem values_bound (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (i : Fin (births F u)) :
    |FlatAffineExceptionalParentBank.values F C h u v a hv i| ≤ (2:ℝ)^height F C h u := by
  have HR := FlatAffineExceptionalParentBank.values_root F C h u v a hv ha i
  have HB := abs_root_lt_coefficientMass_add_one (finitePolynomial F C h u i) (finite_nonzero F C h u i)
    (FlatAffineExceptionalParentBank.values F C h u v a hv i) HR
  have HM : coefficientMass (finitePolynomial F C h u i) ≤ 2^massBound F C h u := by
    simpa only [finitePolynomial,pairFst_pair] using
      FlatAffineExceptionalBankSource.mass_le F C h (pair u (BinaryNatCode.encode i.val))
  have HMR : (coefficientMass (finitePolynomial F C h u i):ℝ) ≤ (2:ℝ)^massBound F C h u := by exact_mod_cast HM
  have HP : 1 ≤ (2:ℝ)^massBound F C h u := one_le_pow₀ (by norm_num)
  unfold height
  rw [pow_succ]
  linarith

theorem normalized_bound (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S+1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (φ : (FlatAffineExceptionalParentBank.bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((FlatAffineExceptionalParentBank.bank F C h S u hm).bank.numerator i) /
      ((FlatAffineExceptionalParentBank.bank F C h S u hm).bank.denominator i:ℝ) =
        FlatAffineExceptionalParentBank.values F C h u v a hv i) (i : Fin (births F u)) :
    |φ ((FlatAffineExceptionalParentBank.bank F C h S u hm).bank.numerator i) /
      ((FlatAffineExceptionalParentBank.bank F C h S u hm).bank.denominator i:ℝ)| ≤ (2:ℝ)^height F C h u := by
  rw [H i]
  exact values_bound F C h u v a hv ha i

theorem cleared_bound (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S+1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (φ : (FlatAffineExceptionalParentBank.bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((FlatAffineExceptionalParentBank.bank F C h S u hm).bank.numerator i) /
      ((FlatAffineExceptionalParentBank.bank F C h S u hm).bank.denominator i:ℝ) =
        FlatAffineExceptionalParentBank.values F C h u v a hv i) (i : Fin (births F u)) :
    |φ (FlatAffineExceptionalParentBank.cleared F C h S u hm i) /
      (FlatAffineExceptionalParentBank.denominator F C h S u hm:ℝ)| ≤ (2:ℝ)^height F C h u := by
  rw [FlatAffineExceptionalParentBank.cleared_recover F C h S u v a hm hv φ H i]
  have HQ : (FlatAffineExceptionalParentBank.denominator F C h S u hm:ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u hm)
  rw [mul_div_cancel_left₀ _ HQ]
  exact values_bound F C h u v a hv ha i

end LeanCanny.Encoding.FlatAffineExceptionalInitialValueBound
