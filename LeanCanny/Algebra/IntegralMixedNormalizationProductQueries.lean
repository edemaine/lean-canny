/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationProductSnapshots
/-! # Fresh inverse-column and raw-row children for normalization products -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

def productLeft (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P id .normalization .frozenConstant .col (get P .target)

def productRight (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P pairFst .rawFactor .companion .row (fun z => get P .target (pairFst z))

theorem productLeft_FP (P : Parameters) (a : Access P) : productLeft P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP .normalization .frozenConstant .col _ (get_binary P a .target)

theorem productRight_FP (P : Parameters) (a : Access P) : productRight P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a pairFst pairFst_mem_FP .rawFactor .companion .row _
    ((get_binary P a .target).comp pairFst_mem_FP)

def productMiddle (P : Parameters) (F : Family) (q : List Bool) : Fin (matrixDimension P F q) :=
  ⟨get P .target q % matrixDimension P F q, Nat.mod_lt _ (matrixDimension_pos P F q)⟩

attribute [local irreducible] inverseMatrixAt rawAt

theorem productLeft_value (P : Parameters) (F : Family) (q : List Bool) :
    inverseMatrixValue P F (productLeft P q) = residueBits
      (inverseMatrix F (IntegralMixedVirtualTaskBits.saved P q) (topRow P F q) (productMiddle P F q) : ZMod (modulus P q)) := by
  unfold productLeft
  rw [inverseMatrix_snapshot,
    IntegralMixedValueFieldQuery.query_saved P id .normalization .frozenConstant .col _ _ (by decide),
    IntegralMixedValueFieldQuery.query_modulus P id .normalization .frozenConstant .col _ _ (by decide),
    IntegralMixedValueFieldQuery.query_field P id .normalization .frozenConstant .col _ _ (by decide) (get_le P .target q),
    IntegralMixedValueFieldQuery.query_other P id .normalization .frozenConstant .col _ _ .row (by decide) (by decide)]
  unfold inverseMatrixAt topRow productMiddle
  rfl

theorem productRight_value (P : Parameters) (F : Family) (q w : List Bool)
    (hh : get P .target q < matrixDimension P F q) (ht : get P .col q < matrixDimension P F q) :
    rawCutValue P F (productRight P (pair q w)) = residueBits
      (rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q)
        (productMiddle P F q) (topCol P F q) : ZMod (modulus P q)) := by
  have HE := IntegralCriticalTotalSnapshotBits.integerEntry_fin
    (rawCoefficient F (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q)) (productMiddle P F q) (topCol P F q)
  have HH : (productMiddle P F q).val = get P .target q := Nat.mod_eq_of_lt hh
  have HT : (topCol P F q).val = get P .col q := Nat.mod_eq_of_lt ht
  rw [HH, HT] at HE
  unfold productRight
  rw [rawAt_snapshot,
    IntegralMixedValueFieldQuery.query_saved P pairFst .rawFactor .companion .row _ _ (by decide),
    IntegralMixedValueFieldQuery.query_modulus P pairFst .rawFactor .companion .row _ _ (by decide),
    IntegralMixedValueFieldQuery.query_field P pairFst .rawFactor .companion .row _ _ (by decide) (get_le P .target (pairFst (pair q w))),
    IntegralMixedValueFieldQuery.query_other P pairFst .rawFactor .companion .row _ _ .col (by decide) (by decide),
    IntegralMixedValueFieldQuery.query_other P pairFst .rawFactor .companion .row _ _ .coefficient (by decide) (by decide)]
  simp only [pairFst_pair]
  unfold rawAt
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) HE

theorem productLeft_frame (P : Parameters) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 5) (hp : 11 < phase q) :
    IntegralMixedRoutineTaskBits.Frame P q (productLeft P q) := by
  have HF := IntegralMixedValueFieldQuery.query_frame_phase P id .normalization .frozenConstant .col (get P .target) q
    (by simpa only [id_eq, IntegralMixedRoutineTaskBits.Routine.code] using hr) hp
  unfold productLeft
  exact HF

theorem productRight_frame (P : Parameters) (q w : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 5) :
    IntegralMixedRoutineTaskBits.Frame P q (productRight P (pair q w)) := by
  have HF := IntegralMixedValueFieldQuery.query_frame_routine P pairFst .rawFactor .companion .row
    (fun z => get P .target (pairFst z)) (pair q w)
    (by simp only [pairFst_pair]; rw [hr]; decide)
  unfold productRight
  simpa only [pairFst_pair] using HF

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits
