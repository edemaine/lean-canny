/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalMixedCleared
public import LeanCanny.Algebra.ModularScalarSpace

/-! # Native actual cleared-height matrices in the initial mixed bank

Canonical retained numerators are proved from the actual integer-root
construction. Clearing a selected height multiplies that generator by the
streamed product omitting its own denominator. Both matrix readers remain
polynomial-space leaves; no modular denominator inversion is used.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open scoped Classical

private theorem integerBank_generators {S B : ℕ} {ι : Type} [Fintype ι]
    (F : IntegralHistorySampler.Sampler S (2 ^ B) 0 ι) (m : ℕ) (p : Fin m → Polynomial ℤ)
    (hp : ∀ i, p i ≠ 0) (hm : m ≤ S + 1) (i : Fin m) :
    (IntegralIntegerRootBank.run F m p hp hm).bank.numerator i =
      (IntegralIntegerRootBank.run F m p hp hm).sampler.scalarPrefix.basis.generator i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    exact (IntegralIntegerRootBank.run F m (fun i => p i.succ) (fun i => hp i.succ) (by omega)).bank.rootStep_generators
      (by omega) ((p 0).map (Int.castRingHom _)) (p 0).natDegree (p 0).leadingCoeff
      (ih (fun i => p i.succ) (fun i => hp i.succ) (by omega)) i

theorem initial_numerator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) :
    (initial F C h S u hm).bank.numerator i = (initial F C h S u hm).sampler.scalarPrefix.basis.generator i :=
  integerBank_generators (FlatAffineExceptionalIntegralPrefix.parentSampler F C S (2 ^ width F u) u)
    (births F u) (finitePolynomial F C h u) (FlatAffineExceptionalBankSource.finite_nonzero F C h u) hm i

theorem cleared_matrix (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1)
    (i : Fin (births F u)) (r t : Fin (FixedWidthPolynomial.count (births F u) (width F u))) :
    Algebra.leftMulMatrix (initial F C h S u hm).sampler.scalarPrefix.basis.finBasis
      (IntegralMixedHistory.cleared (initial F C h S u hm) i) r t =
        omittedDenominator F C h u i *
          Algebra.leftMulMatrix (initial F C h S u hm).sampler.scalarPrefix.basis.finBasis
            ((initial F C h S u hm).sampler.scalarPrefix.basis.generator i) r t := by
  have HE : IntegralMixedHistory.cleared (initial F C h S u hm) i =
      (omittedDenominator F C h u i : (initial F C h S u hm).sampler.scalarPrefix.carrier) *
        (initial F C h S u hm).sampler.scalarPrefix.basis.generator i := by
    change (initial F C h S u hm).bank.numerator i *
      (CommonIntegerDenominator.denominator (Finset.univ.erase i) (initial F C h S u hm).bank.denominator : _) = _
    rw [← omittedDenominator_eq F C h S u hm i, initial_numerator]
    exact mul_comm _ _
  rw [HE]
  exact IntegralActionHeightBounds.int_multiply_entry _ _ _ r t

noncomputable def clearedValue (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : List Bool → ℕ)
    (hm : ∀ q, births F (pairFst q) ≤ S q + 1) (i : ∀ q, Fin (births F (pairFst q)))
    (modulus : List Bool → ℕ)
    (row col : ∀ q, Fin (FixedWidthPolynomial.count (births F (pairFst q)) (width F (pairFst q))))
    (q : List Bool) : List Bool :=
  residueBits ((Algebra.leftMulMatrix (initial F C h (S q) (pairFst q) (hm q)).sampler.scalarPrefix.basis.finBasis
    (IntegralMixedHistory.cleared (initial F C h (S q) (pairFst q) (hm q)) (i q)) (row q) (col q) : ℤ) : ZMod (modulus q))

theorem cleared_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val))
    (S : List Bool → ℕ) (hm : ∀ q, births F (pairFst q) ≤ S q + 1)
    (i : ∀ q, Fin (births F (pairFst q))) (hi : BinaryFn (fun q => (i q).val))
    (modulus : List Bool → ℕ) (hmod : ∀ q, modulus q ≠ 0) (hM : BinaryFn modulus)
    (row col : ∀ q, Fin (FixedWidthPolynomial.count (births F (pairFst q)) (width F (pairFst q))))
    (hR : BinaryFn (fun q => (row q).val)) (hC : BinaryFn (fun q => (col q).val)) :
    SpaceFunction (clearedValue F C h S hm i modulus row col) := by
  have ED := omittedDenominator_evaluator hF C h hh i hi modulus hmod hM
  have EG := generator_evaluator hF C h hh S hm i hi modulus hmod hM row col hR hC
  have E := ModularScalarSpace.mul hM (fun q => (omittedDenominator F C h (pairFst q) (i q) : ZMod (modulus q)))
    (fun q => (Algebra.leftMulMatrix (initial F C h (S q) (pairFst q) (hm q)).sampler.scalarPrefix.basis.finBasis
      ((initial F C h (S q) (pairFst q) (hm q)).sampler.scalarPrefix.basis.generator (i q)) (row q) (col q) : ℤ)) ED EG
  refine E.congr (funext fun q => ?_)
  have H := congrArg (fun z : ℤ => residueBits (z : ZMod (modulus q)))
    (cleared_matrix F C h (S q) (pairFst q) (hm q) (i q) (row q) (col q))
  simp only [Int.cast_mul] at H
  exact H.symm

end LeanCanny.Encoding.FlatAffineExceptionalMixedHistory
