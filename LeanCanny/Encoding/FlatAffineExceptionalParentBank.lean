/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalBankSource
public import LeanCanny.Algebra.IntegralIntegerRootBank
public import LeanCanny.Algebra.CommonIntegerDenominator

/-! # The actual ordinary parent and exceptional scalar in one integral bank

Every retained powered parent coordinate and the independent exceptional
scalar has its actual original integer polynomial. Adjoining these roots
uses one initial scalar-degree cap. The original physical tuple is retained
literally, and common integer denominator clearing supplies algebra elements
for all of its coordinates and the exceptional scalar simultaneously.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalParentBank
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (row parentCone)
open FlatAffineExceptionalBankSource (births width finitePolynomial finite_nonzero)
open IntegralIntegerRootBank (Index)
open scoped Classical BigOperators
attribute [local irreducible] SquareSampleCompleteVertices.candidate

noncomputable def bank (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :
    IntegralIntegerRootBank.State S (width F u) (births F u)
      (Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u)) :=
  IntegralIntegerRootBank.run (FlatAffineExceptionalIntegralPrefix.parentSampler F C S (2 ^ width F u) u)
    (births F u) (finitePolynomial F C h u) (finite_nonzero F C h u) hm

noncomputable def values (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v) : Fin (births F u) → ℝ :=
  Fin.cons (FlatAffineExceptionalSliceFrame.scalar F C h u a)
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val

theorem values_root (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u v a : List Bool)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (i : Fin (births F u)) :
    (finitePolynomial F C h u i).eval₂ (Int.castRingHom ℝ) (values F C h u v a hv i) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have H : values F C h u v a hv (0 : Fin (births F u)) = FlatAffineExceptionalSliceFrame.scalar F C h u a := rfl
    rw [H]
    have HP : finitePolynomial F C h u (0 : Fin (births F u)) = FlatAffineExceptionalIntegralPrefix.polynomial F h u := by
      simp only [finitePolynomial, FlatAffineExceptionalBankSource.polynomial, Fin.val_zero,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ite_true]
    exact (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (FlatAffineExceptionalSliceFrame.scalar F C h u a)) HP).trans
      (FlatAffineExceptionalIntegralPrefix.scalar_root F C h u a ha)
  · rw [FlatAffineExceptionalBankSource.finite_succ]
    exact FlatAffinePowerSampleInput.polynomial_root F u _
      (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).property j

theorem exists_realization (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool)
    (hm : births F u ≤ S + 1) (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a) :
    ∃ y : Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u) → ℝ,
      ∃ φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ((bank F C h S u hm).sampler.rows i).eval₂ (Int.castRingHom ℝ) y = 0) ∧
        (∀ i, y (IntegralIntegerRootBank.old (births F u) i) =
          (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val i) ∧
        (∀ i, φ ((bank F C h S u hm).sampler.scalarPrefix.basis.generator i) =
          y ((bank F C h S u hm).sampler.scalar i) ^ UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i) ∧
        ∀ i, φ ((bank F C h S u hm).bank.numerator i) /
          ((bank F C h S u hm).bank.denominator i : ℝ) = values F C h u v a hv i :=
  IntegralIntegerRootBank.exists_realization (FlatAffineExceptionalIntegralPrefix.parentSampler F C S (2 ^ width F u) u)
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).property
    (births F u) (finitePolynomial F C h u) (finite_nonzero F C h u) hm
    (FlatAffineExceptionalBankSource.finite_degree_cap F C h u) (values F C h u v a hv) (values_root F C h u v a hv ha)

theorem denominator_eq (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) : (bank F C h S u hm).bank.denominator i = (finitePolynomial F C h u i).leadingCoeff :=
  IntegralIntegerRootBank.denominator_run _ _ _ _ _ i

noncomputable def denominator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) : ℤ :=
  CommonIntegerDenominator.denominator Finset.univ (bank F C h S u hm).bank.denominator

theorem denominator_ne_zero (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :
    denominator F C h S u hm ≠ 0 :=
  CommonIntegerDenominator.denominator_ne_zero _ _ (fun i _ => (bank F C h S u hm).denominator_ne_zero i)

noncomputable def cleared (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) : (bank F C h S u hm).sampler.scalarPrefix.carrier :=
  CommonIntegerDenominator.numerator Finset.univ (bank F C h S u hm).bank.denominator
    (bank F C h S u hm).bank.numerator i

theorem cleared_recover (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (bank F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ i, φ ((bank F C h S u hm).bank.numerator i) /
      ((bank F C h S u hm).bank.denominator i : ℝ) = values F C h u v a hv i)
    (i : Fin (births F u)) :
    φ (cleared F C h S u hm i) = (denominator F C h S u hm : ℝ) * values F C h u v a hv i := by
  have HE := (CommonIntegerDenominator.recover φ.toRingHom Finset.univ
    (bank F C h S u hm).bank.denominator (bank F C h S u hm).bank.numerator
    (fun j _ => (bank F C h S u hm).denominator_ne_zero j) i (Finset.mem_univ i)).trans (H i)
  have HZ : (denominator F C h S u hm : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (denominator_ne_zero F C h S u hm)
  exact (div_eq_iff HZ).mp HE |>.trans (mul_comm _ _)

theorem physical_arity (F : Inputs) (u : List Bool) :
    Fintype.card (Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u)) =
      2 * FlatAffineFullSourcePositive.count F u + 1 := by
  rw [IntegralIntegerRootBank.card_index, Fintype.card_fin]
  dsimp only [births]
  omega

theorem physical_arity_unary {F : Inputs} (hF : F.Access) :
    UnaryFn (fun u => Fintype.card (Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u))) :=
  (((UnaryFn.const 2).mul (FlatAffineFullSourcePositive.count_unary hF)).add (UnaryFn.const 1)).of_eq
    (fun u => (physical_arity F u).symm)

end LeanCanny.Encoding.FlatAffineExceptionalParentBank
