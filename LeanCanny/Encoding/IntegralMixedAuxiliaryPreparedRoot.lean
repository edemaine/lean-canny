/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryEmptySpace
/-! # Prepared auxiliary roots retain the original term independently of records

The complete original word is the first field. Chosen chronological records
and advice occupy separate fields. A table with n records fixes the actual
state horizon to n+3, before any geometric sampling trace is constructed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryPreparedRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryParameters IntegralMixedAuxiliarySchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packWords (original rows advice : List Bool) := pair original (pair rows advice)
def pack (original : List Bool) (rows : List (List Bool)) (advice : List Bool) :=
  packWords original (WordList.encode rows) advice

def dimension (n : List Bool → ℕ) (root : List Bool) := n (pairFst root)
def term (t : List Bool → Term) (root : List Bool) := t (pairFst root)

theorem packWords_FP {original rows advice : List Bool → List Bool}
    (ho : original∈FP) (hr : rows∈FP) (ha : advice∈FP) :
    (fun q => packWords (original q) (rows q) (advice q))∈FP := mem_FP_pair ho (mem_FP_pair hr ha)

theorem dimension_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (dimension n) := hn.comp pairFst_mem_FP

theorem term_FP {t : List Bool → Term} (ht : (fun q => (t q).toData.toBits)∈FP) :
    (fun root => (term t root).toData.toBits)∈FP := mem_FP_comp pairFst_mem_FP ht

theorem pack_original (original : List Bool) (rows : List (List Bool)) (advice : List Bool) :
    pairFst (pack original rows advice)=original := pairFst_pair _ _

theorem pack_count (original : List Bool) (rows : List (List Bool)) (advice : List Bool) :
    recordCount (pack original rows advice)=rows.length := by
  simp only [recordCount,records,pack,packWords,pairSnd_pair,pairFst_pair,WordListRecords.count_encode]

theorem pack_horizon (n : List Bool → ℕ) (original : List Bool) (rows : List (List Bool)) (advice : List Bool)
    (hlen : rows.length=n original) : horizon (dimension n) (pack original rows advice)=n original+2 := by
  rw [horizon,pack_count,hlen]
  simp only [dimension,pack_original,max_self]

theorem pack_stateHorizon (n : List Bool → ℕ) (original : List Bool) (rows : List (List Bool)) (advice : List Bool)
    (hlen : rows.length=n original) : stateHorizon (dimension n) (pack original rows advice)=n original+3 := by
  rw [stateHorizon,pack_horizon n original rows advice hlen]

theorem pack_degree (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (rows : List (List Bool)) (advice : List Bool) :
    degreeCharge (dimension n) (term t) (pack original rows advice)=
      (AuxiliaryTiltedTerm.term (n original) (t original)).toData.size := by
  simp only [degreeCharge,augmented,dimension,term,pack_original]

theorem pack_width (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (rows : List (List Bool)) (advice : List Bool) :
    scalarWidth (dimension n) (term t) (pack original rows advice)=
      (IntegralMixedExceptionalBounds.auxiliaryCap (n original+3)
        (FixedLeadingTiltedSource.degree (AuxiliaryTiltedTerm.term (n original) (t original)).toData.size)).size := by
  simp only [scalarWidth,scalarCeiling,spatialDegree,pack_degree,dimension,pack_original]

theorem pack_seed (n : List Bool → ℕ) (t : List Bool → Term) (original : List Bool)
    (rows : List (List Bool)) (advice : List Bool) :
    seed (dimension n) (term t) (pack original rows advice)=
      LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.originalSeed (n original)
        (AuxiliaryTiltedTerm.term (n original) (t original)).toData.size 0 (t original) := by
  simp only [seed,pack_degree,dimension,term,pack_original]

theorem model_space {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q) :
    SpaceFunction (IntegralMixedAuxiliaryEmptyPlan.machine (dimension_unary hn) (term_FP ht)
      (fun root => ha (pairFst root))).model :=
  IntegralMixedAuxiliaryEmptyPlan.model_space (dimension_unary hn) (term_FP ht) (fun root => ha (pairFst root))
end LeanCanny.Encoding.IntegralMixedAuxiliaryPreparedRoot
