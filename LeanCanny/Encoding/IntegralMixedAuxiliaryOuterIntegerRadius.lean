/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
/-! # Radius metadata is separate from the original record table

Context is pair(candidatePacket, pair(recordWords, requestedRadiusBits)).
The interpreted outer radius never parses record bytes as part of a number.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (original)
set_option backward.isDefEq.respectTransparency false

def requested (context : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd context))

theorem requested_binary : BinaryFn requested :=
  BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def radius {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (context : List Bool) :=
  max (IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original context)) (requested context)

theorem radius_binary {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) : BinaryFn (radius hn ht ha) := by
  have HC:BinaryFn (fun c=>IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original c)) :=
    (IntegralMixedAuxiliaryCandidateRadius.radius_binary hn ht ha).comp IntegralMixedAuxiliaryMarkedIntegerPlan.original_FP
  exact (BinaryFn.ite (HC.le requested_binary) requested_binary HC).of_eq (fun c=>by
    change (if _≤requested c then requested c else _)=max _ (requested c)
    by_cases h:IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original c)≤requested c
    · rw [ite_eq_left h,max_eq_right h]
    · rw [ite_eq_right h,max_eq_left (by omega)])

theorem radius_candidate {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (context : List Bool) :
    IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original context)≤radius hn ht ha context := le_max_left _ _

theorem radius_requested {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (context : List Bool) :
    requested context≤radius hn ht ha context := le_max_right _ _

theorem requested_at (candidate records : List Bool) (R : ℕ) :
    requested (pair candidate (pair records (BinaryNatCode.encode R)))=R := by
  simp only [requested,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem radius_at {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (candidate records : List Bool) (R : ℕ) :
    radius hn ht ha (pair candidate (pair records (BinaryNatCode.encode R)))=
      max (IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (pairFst candidate)) R := by
  simp only [radius,requested_at,original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair]

end LeanCanny.Encoding.IntegralMixedAuxiliaryOuterIntegerSource
