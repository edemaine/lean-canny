/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliarySchedule
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Causal original fields at the complete saved-birth key -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliarySchedule
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryParameters
set_option backward.isDefEq.respectTransparency false

def savedPacket (n : List Bool → ℕ) (t : List Bool → Term) (key : List Bool) :=
  pair (pairFst key) (List.replicate (IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) key) true)

theorem savedPacket_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) : savedPacket n t∈FP :=
  mem_FP_pair pairFst_mem_FP
    ((IntegralMixedFullHistoryFamilyBits.prefix_unary (parameters n t) (access hn ht)).replicate_mem_FP true)

theorem frozen_saved_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    UnaryFn (fun key => frozen n (pairFst key)
      (IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) key)) :=
  ((frozen_packet_unary hn).comp (savedPacket_FP hn ht)).of_eq (fun key => by
    simp only [savedPacket,pairFst_pair,pairSnd_pair,List.length_replicate])

theorem exponent_saved_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    BinaryFn (fun key => levelExponent n t (pairFst key)
      (IntegralMixedFramedHistoryFamilyBits.prefixLength (parameters n t) key)) := by
  have H : BinaryFn (fun key => levelExponent n t (pairFst (savedPacket n t key))
      (pairSnd (savedPacket n t key)).length) :=
    (levelExponent_packet_binary hn ht).comp (savedPacket_FP hn ht)
  exact H.of_eq (fun key => by
    simp only [savedPacket,pairFst_pair,pairSnd_pair,List.length_replicate])

theorem tilt_saved_unary {n : List Bool → ℕ} (hn : UnaryFn n) :
    UnaryFn (fun key => n (pairFst key)) := hn.comp pairFst_mem_FP

theorem term_saved_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun root => (t root).toData.toBits)∈FP) :
    (fun key => (augmented n t (pairFst key)).toData.toBits)∈FP :=
  mem_FP_comp pairFst_mem_FP (LeanCanny.Geometry.CanonicalAuxiliaryTrajectory.auxiliaryTerm_FP hn ht)

theorem source_scope (n : List Bool → ℕ) (t : List Bool → Term) (ha : ∀ root,(t root).arity≤n root)
    (root : List Bool) : (augmented n t root).arity+1≤(parameters n t).ambient root := by
  rw [augmented_arity n t ha]
  exact Nat.le_refl _

theorem tilt_scope (n : List Bool → ℕ) (t : List Bool → Term) (root : List Bool) :
    n root+2=(parameters n t).ambient root := rfl
end LeanCanny.Encoding.IntegralMixedAuxiliarySchedule
