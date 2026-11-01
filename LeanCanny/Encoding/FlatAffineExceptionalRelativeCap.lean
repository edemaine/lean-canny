/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
public import LeanCanny.Algebra.IntegralMixedExceptionalBounds

/-! # One enlarged initial cap for the actual relative exceptional route

Original integer parent/scalar leaves and every constructed relative sweep
auxiliary degree are covered BEFORE constructing the first integral bank.
The retained parent and exceptional scalar are unchanged. Later sweep caps
come from the original spatial source, rather than recomputed absolute norms.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalRelativeCap
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births finitePolynomial)
open IntegralMixedHistory IntegralMixedHistoryScript
open scoped Classical

noncomputable def auxiliaryCap (F : Inputs) (u : List Bool) : ℕ :=
  IntegralMixedExceptionalBounds.auxiliaryCap (arity F u) (FlatAffinePowerControls.degree F u)

noncomputable def width (F : Inputs) (u : List Bool) : ℕ :=
  (FlatAffineExceptionalBankSource.degreeBound F u + auxiliaryCap F u).size

theorem auxiliaryCap_binary {F : Inputs} (hF : F.Access) : BinaryFn (auxiliaryCap F) :=
  IntegralMixedExceptionalBounds.auxiliaryCap_binary (FlatAffineFullSourceTower.arity_unary hF)
    (BinaryFn.ofUnary (FlatAffinePowerControls.degree_unary hF.source))

theorem width_unary {F : Inputs} (hF : F.Access) (h : (u : List Bool) → Fin (arity F u)) : UnaryFn (width F) :=
  (UnaryFn.length ((FlatAffineExceptionalBankSource.degreeBound_binary hF h).add (auxiliaryCap_binary hF)).bits_mem_FP).of_eq
    (fun _ => BinaryNatCode.length_encode _)

theorem auxiliary_cap (F : Inputs) (u : List Bool) : auxiliaryCap F u ≤ 2 ^ width F u :=
  (Nat.le_add_left _ _).trans (Nat.lt_size_self _).le

theorem relative_cap (F : Inputs) (u : List Bool) :
    PurePowerReductionBounds.dimension (arity F u) (FlatAffinePowerControls.degree F u) ≤ 2 ^ width F u := by
  have H : PurePowerReductionBounds.dimension (arity F u) (FlatAffinePowerControls.degree F u) ≤ auxiliaryCap F u := by
    unfold auxiliaryCap IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedExceptionalBounds.K
    omega
  exact H.trans (auxiliary_cap F u)

theorem finite_degree_cap (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (i : Fin (births F u)) :
    (finitePolynomial F C h u i).natDegree ≤ 2 ^ width F u := by
  have H := FlatAffineExceptionalBankSource.degree_le F C h (pair u (BinaryNatCode.encode i.val))
  rw [pairFst_pair] at H
  exact H.trans ((Nat.le_add_right _ _).trans (Nat.lt_size_self _).le)

noncomputable def integerBank (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :=
  IntegralIntegerRootBank.run (FlatAffineExceptionalIntegralPrefix.parentSampler F C S (2 ^ width F u) u)
    (births F u) (finitePolynomial F C h u) (FlatAffineExceptionalBankSource.finite_nonzero F C h u) hm

noncomputable def initial (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :=
  retainIntegerBank (P := FlatAffineExceptionalMixedHistory.spatialSource F u) (integerBank F C h S u hm) (relative_cap F u)

theorem exists_realization (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S + 1)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid
      (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a) :
    ∃ y : IntegralIntegerRootBank.Index (Fin (FlatAffineFullSourcePositive.count F u)) (births F u) → ℝ,
      ∃ φ : (initial F C h S u hm).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ((initial F C h S u hm).sampler.rows i).eval₂ (Int.castRingHom ℝ) y = 0) ∧
        (∀ i, y (IntegralIntegerRootBank.old (births F u) i) =
          (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val i) ∧
        (∀ i, φ ((initial F C h S u hm).sampler.scalarPrefix.basis.generator i) =
          y ((initial F C h S u hm).sampler.scalar i) ^ UniformIntegralPowerSchedule.weights S (2 ^ width F u) (births F u) i) ∧
        ∀ i, φ ((initial F C h S u hm).bank.numerator i) / ((initial F C h S u hm).bank.denominator i : ℝ) =
          FlatAffineExceptionalParentBank.values F C h u v a hv i :=
  IntegralIntegerRootBank.exists_realization (FlatAffineExceptionalIntegralPrefix.parentSampler F C S (2 ^ width F u) u)
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).val
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F (parentCone F C)) u v hv).property
    (births F u) (finitePolynomial F C h u) (FlatAffineExceptionalBankSource.finite_nonzero F C h u) hm
    (finite_degree_cap F C h u) (FlatAffineExceptionalParentBank.values F C h u v a hv)
    (FlatAffineExceptionalParentBank.values_root F C h u v a hv ha)

end LeanCanny.Encoding.FlatAffineExceptionalRelativeCap
