/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Basic
public import Mathlib.Data.Fintype.Powerset
/-! # Finite monotone combinations of closed predicates are closed -/
@[expose] public section
namespace LeanCanny.Geometry.FiniteMonotoneClosed
open Set
open scoped Classical
variable {X I : Type*} [TopologicalSpace X] [Fintype I]

theorem isClosed (A : I → Set X) (hA : ∀ i, IsClosed (A i)) (P : (I → Prop) → Prop)
    (HM : ∀ a b : I → Prop, (∀ i, a i → b i) → P a → P b) :
    IsClosed {x | P (fun i => x ∈ A i)} := by
  have HE : {x | P (fun i => x ∈ A i)} =
      ⋃ s : Finset I, {x | P (fun i => i ∈ s) ∧ ∀ i ∈ s, x ∈ A i} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion]
    constructor
    · intro H
      refine ⟨Finset.univ.filter (fun i => x ∈ A i),?_,?_⟩
      · exact HM _ _ (fun i H => Finset.mem_filter.mpr ⟨Finset.mem_univ i,H⟩) H
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
    · rintro ⟨s,hs,hx⟩
      exact HM _ _ hx hs
  rw [HE]
  apply isClosed_iUnion_of_finite
  intro s
  by_cases HS : P (fun i => i ∈ s)
  · have HE : {x | P (fun i => i ∈ s) ∧ ∀ i ∈ s, x ∈ A i} = ⋂ i ∈ s, A i := by
      ext x
      simp only [mem_ofPred_eq,HS,true_and,mem_iInter]
    rw [HE]
    exact isClosed_biInter (fun i _ => hA i)
  · have HE : {x | P (fun i => i ∈ s) ∧ ∀ i ∈ s, x ∈ A i} = ∅ := by simp [HS]
    rw [HE]
    exact isClosed_empty

end LeanCanny.Geometry.FiniteMonotoneClosed
