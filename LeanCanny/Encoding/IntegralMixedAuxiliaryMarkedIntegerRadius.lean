/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerRealization
/-! # Independent original outer radii with a certified candidate lower bound

Only the second context field carries the requested binary radius. No vertex
label is enlarged and no prelude degree, width or horizon depends on it.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (original)
open scoped Classical

noncomputable def radius {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (context : List Bool) :=
  let base:=IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original context)
  let requested:=Nat.fromBitsLE (pairSnd context)
  if requested<base then base else requested

theorem radius_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) : BinaryFn (radius hn ht ha) := by
  have HB : BinaryFn (fun c=>IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original c)) :=
    (IntegralMixedAuxiliaryCandidateRadius.radius_binary hn ht ha).comp original_FP
  have HR : BinaryFn (fun c=>Nat.fromBitsLE (pairSnd c)) := BinaryFn.fromBits pairSnd_mem_FP
  exact BinaryFn.ite (HR.lt HB) HB HR

theorem candidate_radius_le {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (context : List Bool) :
    IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (original context)≤radius hn ht ha context := by
  dsimp only [radius]
  split_ifs <;> omega

theorem requested_radius_le {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) (context : List Bool) :
    Nat.fromBitsLE (pairSnd context)≤radius hn ht ha context := by
  dsimp only [radius]
  split_ifs <;> omega

theorem radius_at {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    (old requested : List Bool) : radius hn ht ha (pair old requested)=
      max (IntegralMixedAuxiliaryCandidateRadius.radius hn ht ha (pairFst old)) (Nat.fromBitsLE requested) := by
  simp only [radius,original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,pairFst_pair,pairSnd_pair]
  split_ifs <;> omega

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
