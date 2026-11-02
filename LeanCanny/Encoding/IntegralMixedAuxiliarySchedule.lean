/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryParameters
/-! # Native causal level fields from original syntax and a unary scalar birth

The seed covers every tilted LOW word of the once-augmented term. The exact
level exponent uses the preceding bank-height recurrence, never a later bank
or a serialized level integer. No current-bank reader is a control field.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliarySchedule
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

def seed (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  originalSeed (n root) (degreeCharge n t root) 0 (t root)
def stateHorizon (n : List Bool → ℕ) (root : List Bool) := horizon n root+1

def factor (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :=
  sourceFactor (n root) (stateHorizon n root) (scalarWidth n t root) (degreeCharge n t root)+2

def height (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) (birth : ℕ) :=
  recursiveHeight (n root) (stateHorizon n root) (scalarWidth n t root) (degreeCharge n t root)
    (seed n t root) birth

def levelExponent (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) (birth : ℕ) :=
  LeanCanny.Geometry.IntegralMixedCausalLevelCapacity.exponent (n root+1) (degreeCharge n t root)
    (FixedWidthPolynomial.count birth (scalarWidth n t root)) (height n t root birth)

def frozen (n : List Bool → ℕ) (root : List Bool) (birth : ℕ) := min birth (n root)

theorem seed_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : BinaryFn (seed n t) :=
  originalSeed_binary hn (degreeCharge_unary hn ht) (BinaryFn.const 0) ht
    (fun root => (augmented n t root).degreeBound_le_dataSize)

theorem factor_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : BinaryFn (factor n t) :=
  (sourceFactor_binary hn ((horizon_unary hn).add (UnaryFn.const 1))
    (scalarWidth_unary hn ht) (BinaryFn.ofUnary (degreeCharge_unary hn ht))).add (BinaryFn.const 2)

theorem height_packet_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    BinaryFn (fun p => height n t (pairFst p) (pairSnd p).length) :=
  recursiveHeight_binary (hn.comp pairFst_mem_FP)
    (((horizon_unary hn).add (UnaryFn.const 1)).comp pairFst_mem_FP)
    ((scalarWidth_unary hn ht).comp pairFst_mem_FP)
    ((BinaryFn.ofUnary (degreeCharge_unary hn ht)).comp pairFst_mem_FP)
    ((seed_binary hn ht).comp pairFst_mem_FP) UnaryFn.index

theorem rank_packet_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    BinaryFn (fun p => FixedWidthPolynomial.count (pairSnd p).length (scalarWidth n t (pairFst p))) :=
  ((BinaryFn.const 2).powUnary ((scalarWidth_unary hn ht).comp pairFst_mem_FP)).powUnary UnaryFn.index

theorem levelExponent_packet_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    BinaryFn (fun p => levelExponent n t (pairFst p) (pairSnd p).length) :=
  (((BinaryFn.ofUnary ((hn.comp pairFst_mem_FP).add (UnaryFn.const 1))).size).add
    ((IntegralMixedRetainedRealBound.height_binary (rank_packet_binary hn ht) (height_packet_binary hn ht)).mul
      ((BinaryFn.ofUnary (spatialDegree_unary hn ht)).comp pairFst_mem_FP))).add (BinaryFn.const 2)

theorem frozen_packet_unary {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn (fun p => frozen n (pairFst p) (pairSnd p).length) :=
  UnaryFn.index.min (hn.comp pairFst_mem_FP)

theorem height_positive (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) (birth : ℕ) :
    1≤height n t root birth := recursiveHeight_positive _ _ _ _ _ _

theorem word_le_height (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) (birth : ℕ) :
    (FixedLeadingTiltedSource.lowTerm (frozen n root birth) (degreeCharge n t root) (n root)
      (augmented n t root)).toData.size≤height n t root birth :=
  word_le_recursiveHeight _ _ _ _ _ 0 _ _ (min_le_right _ _)

theorem frozen_le (n : List Bool → ℕ) (root : List Bool) (birth : ℕ) : frozen n root birth≤n root := min_le_right _ _
theorem frozen_birth (n : List Bool → ℕ) (root : List Bool) (birth : ℕ) (hb : birth≤n root) : frozen n root birth=birth := min_eq_left hb
end LeanCanny.Encoding.IntegralMixedAuxiliarySchedule
