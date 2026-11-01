/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalActualOriginalLeaf
public import LeanCanny.Algebra.IntegralCriticalActualFactorModel
/-! # Concrete original and derivative coefficient values at flat leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalActualCoefficientModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits IntegralCriticalActualFactorModel IntegralCriticalActualLowMatrixModel
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap

noncomputable def coefficientMatrix (S : IntegralClearedCoefficientBits.Source) (q : List Bool) (k : ℕ) :
    Matrix (Fin (S.rank q)) (Fin (S.rank q)) (ZMod (S.modulus q)) := by
  let := S.ring q
  exact (Algebra.leftMulMatrix (S.basis q) ((S.polynomial q).coeff
    (RationalSubstitution.Indexed.exponentVector (S.arity q) (FixedWidthPolynomial.entry (S.sourceWidth q) k)))).map
      (Int.castRingHom (ZMod (S.modulus q)))
noncomputable def originalAt (A : IntegralHistoryCriticalBits.Family) (k m : ℕ) (hm : m ≠ 0) (r t : ℕ) :=
  factorAt A 0 0 k m hm 0 r t
noncomputable def derivativeAt (A : IntegralHistoryCriticalBits.Family) (j k m : ℕ) (hm : m ≠ 0) (r t : ℕ) :=
  factorAt A 1 j k m hm 0 r t
noncomputable def original (F : Scripts) (q : List Bool) :=
  originalAt (IntegralCriticalTotalCreatingBits.atFamily F q) (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q) (IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q)
noncomputable def derivative (F : Scripts) (q : List Bool) :=
  derivativeAt (IntegralCriticalTotalCreatingBits.atFamily F q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q)
    (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q)
    (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q % rank F q) (IntegralCriticalHistoryTask.get F.toParameters .col q % rank F q)

theorem rank_euler (F : Scripts) (q : List Bool) : rank F q = (IntegralCriticalTotalCreatingBits.euler F).rank q := by
  change (IntegralCriticalTotalCreatingBits.euler F).rank (pairFst (IntegralCriticalFlatGridBits.termInput F.toParameters q)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent]

theorem original_snapshot (F : Scripts) (q : List Bool) (k r t : ℕ) :
    originalAt (IntegralCriticalTotalCreatingBits.atFamily F q) k
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) r t =
    entryBits (coefficientMatrix (IntegralCriticalTotalCreatingBits.CoefficientLeaves.original F) q k) r t := rfl

theorem derivative_snapshot (F : Scripts) (q : List Bool) (k r t : ℕ) :
    derivativeAt (IntegralCriticalTotalCreatingBits.atFamily F q) (IntegralCriticalHistoryTask.get F.toParameters .derivative q) k
      (IntegralCriticalHistoryTask.modulus F.toParameters q) (IntegralCriticalHistoryTask.modulus_ne_zero F.toParameters q) r t =
    entryBits (coefficientMatrix (IntegralDerivativeBits.clearedSource (IntegralCriticalTotalCreatingBits.CoefficientLeaves.derivative F)) q k) r t := rfl

noncomputable def leaf (F : Scripts) :=
  IntegralCriticalTotalCreatingBits.CoefficientLeaves.originalValue F (IntegralCriticalActualOriginalLeaf.scalar F)

theorem leaf_eq (F : Scripts) (q : List Bool) : leaf F q = original F q := by
  have H := IntegralCriticalTotalCreatingBits.CoefficientLeaves.originalValue_actual F
    (IntegralCriticalActualOriginalLeaf.scalar F) (IntegralCriticalActualOriginalLeaf.scalar_packet F) q
  unfold original
  rw [original_snapshot, rank_euler]
  exact H.trans (entryBits_fin
    (coefficientMatrix (IntegralCriticalTotalCreatingBits.CoefficientLeaves.original F) q
      (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q))
    (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (IntegralCriticalTotalCreatingBits.CoefficientLeaves.original F) .row q)
    (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (IntegralCriticalTotalCreatingBits.CoefficientLeaves.original F) .col q)).symm


theorem original_FP (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F)
    (a : IntegralCriticalActualOriginalLeaf.Access F) : original F ∈ FP :=
  mem_FP_of_eq
    (IntegralCriticalTotalCreatingBits.CoefficientLeaves.originalValue_FP F h.task h.metadata h.objective
      (IntegralCriticalActualOriginalLeaf.scalar F) (IntegralCriticalActualOriginalLeaf.scalar_FP F h.task a))
    (leaf_eq F)

theorem original_space (F : Scripts) (h : IntegralCriticalFlatActualSources.Controls F)
    (a : SpaceFunction (IntegralCriticalActualOriginalLeaf.rawReader F)) : SpaceFunction (original F) :=
  (IntegralCriticalTotalCreatingBits.CoefficientLeaves.originalValue_space F h.task h.metadata h.objective
    (IntegralCriticalActualOriginalLeaf.scalar F) (IntegralCriticalActualOriginalLeaf.scalar_space F h.task a)).congr
    (funext (leaf_eq F))

end LeanCanny.Algebra.IntegralCriticalActualCoefficientModel
