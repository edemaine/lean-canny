/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutBounds
public import LeanCanny.Algebra.PaddedIntegralSelectedMatrixSource

/-! # Charged native leading and inverse stages for actual relative cuts

The source is the actual tagged relative factor over its creating prefix,
with an explicit truncation guard. Only RAW factor-matrix requests remain
children. The integer leading is computed by a characteristic trailing
scan, and the inverse matrix by streamed characteristic coefficients and
matrix powers. Neither result is a supplied scalar or coefficient oracle.

Raw coordinate/PSC/Gram matrix construction and its original-source height
bound remain separate obligations. This module does not assert their
native space bounds or add relative cuts to the mixed script interpreter.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts IntegralMixedCutMatrix
open scoped Classical

structure Family where
  ambient : List Bool → ℕ
  cap : List Bool → ℕ
  width : List Bool → ℕ
  birth : List Bool → ℕ
  physical : List Bool → Type
  spatial : (q : List Bool) → SpatialSource (ambient q)
  state : (q : List Bool) → State (spatial q) (cap q) (width q) (birth q) (physical q)
  birth_bound : ∀ q, birth q ≤ cap q
  rule : (q : List Bool) → Rule (ambient q)
  kind : (q : List Bool) → Kind (spatial q) (rule q)
  degree : List Bool → ℕ
  degree_bound : ∀ q, degree q ≤ IntegralMixedExceptionalBounds.auxiliaryCap (ambient q + 1) (spatial q).degree
  scalar_cap : ∀ q, IntegralMixedExceptionalBounds.auxiliaryCap (ambient q + 1) (spatial q).degree ≤ 2 ^ width q

noncomputable def source (F : Family) : PaddedIntegralGeneratorSource.Source where
  arity := F.birth
  width := F.width
  carrier q := (F.state q).sampler.scalarPrefix.carrier
  ring q := (F.state q).sampler.scalarPrefix.ring
  nontrivial q := (F.state q).sampler.scalarPrefix.nontrivial
  basis q := (F.state q).sampler.scalarPrefix.basis
  polynomial q := raw (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)
  degree := F.degree

theorem source_coefficient (F : Family) (q : List Bool) (k : ℕ) :
    (source F).coefficient q k =
      if k ≤ F.degree q then coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) k else 0 :=
  raw_coefficient_matrix _ _ _ _ _ _

structure RawBounds (F : Family) where
  height : List Bool → ℕ
  bound : ∀ q k i j,
    (coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) k i j).natAbs ≤ 2 ^ height q

noncomputable def selectedBounds (F : Family) (H : RawBounds F) :
    PaddedIntegralSelectedMatrixSource.Bounds (source F) where
  height := H.height
  selected q i j := by
    change (IntegralRelativeNormalizationMatrix.top (F.state q).sampler.scalarPrefix.basis.finBasis
      (raw (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)) (F.degree q) i j).natAbs ≤ _
    rw [top_eq]
    exact H.bound q (F.degree q) i j

structure Controls (F : Family) where
  birth : UnaryFn F.birth
  width : UnaryFn F.width
  degree : BinaryFn F.degree

structure RawRequests (F : Family) where
  request : List Bool → List Bool
  correct : ∀ q mw k (i j : Fin (count (F.birth q) (F.width q))),
    request (pair (pair q mw) (pair (BinaryNatCode.encode k)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((coefficientMatrix (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) k i j : ℤ) :
        ZMod (Nat.fromBitsLE mw + 1))

def coefficientIndex (q : List Bool) := Nat.fromBitsLE (pairFst (pairSnd q))

theorem coefficientIndex_binary : BinaryFn coefficientIndex :=
  BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

def entry (F : Family) (R : RawRequests F) (q : List Bool) : List Bool :=
  if coefficientIndex q ≤ F.degree (PaddedIntegralGeneratorSource.base q) then R.request q else []

noncomputable def access (F : Family) (a : Controls F) (R : RawRequests F) :
    PaddedIntegralGeneratorSource.Access (source F) where
  arity := a.birth
  width := a.width
  degree := a.degree
  entry := entry F R
  entry_eq q mw k i j := by
    simp only [entry, coefficientIndex, PaddedIntegralGeneratorSource.base, pairFst_pair,
      pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [source_coefficient]
    split_ifs with H
    · exact R.correct q mw k i j
    · simp only [residueBits, BinaryNatCode.encode]
      rfl

theorem entry_evaluator (F : Family) (a : Controls F) (R : RawRequests F)
    (E : SpaceFunction R.request) : SpaceFunction (entry F R) := by
  have HP := coefficientIndex_binary.le (a.degree.comp PaddedIntegralGeneratorSource.base_FP)
  exact (SpaceFunction.branch _ HP.flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (by funext q; simp only [entry, decide_eq_true_eq, Function.comp_apply])

noncomputable def leading (F : Family) (H : RawBounds F) : List Bool → List Bool :=
  PaddedIntegralSelectedMatrixSource.denominatorValue (source F) (selectedBounds F H)

theorem leading_evaluator (F : Family) (a : Controls F) (R : RawRequests F)
    (H : RawBounds F) (hH : BinaryFn H.height) (E : SpaceFunction R.request) : SpaceFunction (leading F H) :=
  PaddedIntegralSelectedMatrixSource.denominator_evaluator (source F) (selectedBounds F H)
    (access F a R) hH (entry_evaluator F a R E)

attribute [local irreducible] PaddedIntegralSelectedMatrixSource.integerFamily

theorem leading_packet (F : Family) (H : RawBounds F) (q mw tail : List Bool) :
    leading F H (pair (pair q mw) tail) =
      residueBits ((normalizedScalarLeading (F.state q)
        (raw (F.state q) (F.birth_bound q) (F.rule q) (F.kind q) (F.degree q)) (F.degree q) : ℤ) :
          ZMod (Nat.fromBitsLE mw + 1)) := by
  generalize HP : pair (pair q mw) tail = p
  have HB : PaddedIntegralGeneratorSource.base p = q := by
    rw [← HP]
    simp only [PaddedIntegralGeneratorSource.base, pairFst_pair]
  have HM : PaddedIntegralGeneratorSource.modulus p = mw := by
    rw [← HP]
    simp only [PaddedIntegralGeneratorSource.modulus, pairFst_pair, pairSnd_pair]
  subst q
  subst mw
  change IntegralParameterInverseBits.denominatorValue
    (PaddedIntegralSelectedMatrixSource.integerFamily (source F) (selectedBounds F H))
      (pair p (PaddedIntegralGeneratorSource.modulus p)) = _
  rw [IntegralParameterInverseBits.denominatorValue, pairFst_pair, pairSnd_pair]
  unfold PaddedIntegralSelectedMatrixSource.integerFamily
  change residueBits ((IntegralParameterInverse.denominator
    ((source F).coefficient (PaddedIntegralGeneratorSource.base p) (F.degree (PaddedIntegralGeneratorSource.base p))).charpoly : ℤ) :
      ZMod (Nat.fromBitsLE (PaddedIntegralGeneratorSource.modulus p) + 1)) = _
  rw [source_coefficient, ite_eq_left (Nat.le_refl _), leading_eq]
  rfl

theorem inverse_evaluator (F : Family) (a : Controls F) (R : RawRequests F)
    (H : RawBounds F) (hH : BinaryFn H.height) (E : SpaceFunction R.request) :
    SpaceFunction (PaddedIntegralSelectedMatrixSource.value (source F) (selectedBounds F H)) :=
  PaddedIntegralSelectedMatrixSource.evaluator (source F) (selectedBounds F H)
    (access F a R) hH (entry_evaluator F a R E)

theorem request_birth_lt (F : Family) (q : List Bool) : F.birth q < F.birth q + 1 := Nat.lt_succ_self _

theorem degree_cap (F : Family) (q : List Bool) : (source F).degree q ≤ 2 ^ F.width q :=
  (F.degree_bound q).trans (F.scalar_cap q)

end LeanCanny.Algebra.IntegralMixedCutSource
