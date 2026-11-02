/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryWordBudget
public import LeanCanny.Encoding.WordListRecords
public import LeanCanny.Algebra.IntegralCriticalHistoryTask
/-! # Native task geometry from original auxiliary syntax

The degree charge uses the auxiliary term exactly once. Scalar width is the
binary length of the original auxiliary degree ceiling. The horizon covers
both every supplied record and every original coordinate; neither interpreted
bank heights nor coefficient evaluators occur in this layout.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryParameters
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
set_option backward.isDefEq.respectTransparency false

def records (root : List Bool) := pairFst (pairSnd root)
def recordCount (root : List Bool) := WordListRecords.count (records root)
def augmented (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  AuxiliaryTiltedTerm.term (n root) (t root)
def degreeCharge (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  (augmented n t root).toData.size

def spatialDegree (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  FixedLeadingTiltedSource.degree (degreeCharge n t root)
def scalarCeiling (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  IntegralMixedExceptionalBounds.auxiliaryCap (n root+3) (spatialDegree n t root)
def scalarWidth (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  (scalarCeiling n t root).size

def horizon (n : List Bool → ℕ) (root : List Bool) := max (n root) (recordCount root)+2

def parameters (n : List Bool → ℕ) (t : List Bool → Term) : Parameters where
  cap := horizon n
  width := scalarWidth n t
  ambient root := n root+2
  sourceWidth root := (spatialDegree n t root).size
  degree := spatialDegree n t
  height _ := 0
  modulusBound _ := 2

theorem recordCount_unary : UnaryFn recordCount :=
  WordListRecords.count_unary.comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem degreeCharge_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : UnaryFn (degreeCharge n t) :=
  augmentedDegree_unary hn ht

theorem spatialDegree_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : UnaryFn (spatialDegree n t) :=
  ((UnaryFn.const 4).mul (degreeCharge_unary hn ht)).add (UnaryFn.const 2)

theorem scalarCeiling_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : BinaryFn (scalarCeiling n t) :=
  IntegralMixedExceptionalBounds.auxiliaryCap_binary (hn.add (UnaryFn.const 3))
    (BinaryFn.ofUnary (spatialDegree_unary hn ht))

theorem scalarWidth_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : UnaryFn (scalarWidth n t) :=
  (UnaryFn.length (scalarCeiling_binary hn ht).bits_mem_FP).of_eq
    (fun root => BinaryNatCode.length_encode (scalarCeiling n t root))

theorem sourceWidth_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    UnaryFn (fun root => (spatialDegree n t root).size) :=
  (UnaryFn.length (BinaryFn.ofUnary (spatialDegree_unary hn ht)).bits_mem_FP).of_eq
    (fun root => BinaryNatCode.length_encode (spatialDegree n t root))

theorem horizon_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (horizon n) :=
  (hn.max recordCount_unary).add (UnaryFn.const 2)

attribute [local irreducible] degreeCharge spatialDegree scalarCeiling scalarWidth horizon

theorem access {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : Access (parameters n t) where
  cap := horizon_unary hn
  width := scalarWidth_unary hn ht
  ambient := hn.add (UnaryFn.const 2)
  sourceWidth := sourceWidth_unary hn ht
  degree := BinaryFn.ofUnary (spatialDegree_unary hn ht)
  height := BinaryFn.const 0
  modulusBound := BinaryFn.const 2

theorem auxiliary_cap (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((parameters n t).ambient root+1) ((parameters n t).degree root) ≤
      2^(parameters n t).width root := by
  change IntegralMixedExceptionalBounds.auxiliaryCap (n root+2+1) (spatialDegree n t root) ≤ 2^scalarWidth n t root
  unfold scalarWidth scalarCeiling
  exact (Nat.lt_size_self _).le

theorem room (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    recordCount root+2≤(parameters n t).cap root+1 := by
  unfold parameters horizon
  change recordCount root+2≤max (n root) (recordCount root)+2+1
  have H:=le_max_right (n root) (recordCount root)
  omega

theorem original_coordinates (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    n root≤(parameters n t).cap root := by
  unfold parameters horizon
  exact (le_max_left _ _).trans (Nat.le_add_right _ _)

theorem ambient_positive (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    0<(parameters n t).ambient root := by change 0<n root+2; omega

theorem source_width (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    ((parameters n t).degree root).size≤(parameters n t).sourceWidth root := Nat.le_refl _

theorem degree_two (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    2≤(parameters n t).degree root := by
  unfold parameters spatialDegree FixedLeadingTiltedSource.degree
  change 2≤4*degreeCharge n t root+2
  omega

theorem augmented_arity (n : List Bool → ℕ) (t : List Bool → Term) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool) : (augmented n t root).arity=n root+1 := by
  rw [augmented,AuxiliaryTiltedTerm.arity,max_eq_right (by have H:=ha root; omega)]
end LeanCanny.Encoding.IntegralMixedAuxiliaryParameters
