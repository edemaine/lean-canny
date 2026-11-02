/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryCandidatePoint

/-! # Decoded candidate points meet every nonempty original clopen piece

The sample is the point of the literal decoded joint vertex. The theorem
retains its original-equation membership, which validity alone does not imply.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryRecipeRoot
open LeanCanny.Geometry.CoerciveComponentSampling
open AuxiliaryTiltedTerm (polynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def pointAt {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original label : List Bool) (hv : Valid hn ht ha (pair original label)) : Fin (n original)→ℝ :=
  fun i=>point hn ht ha (pair original label) hv ⟨i.val,by simpa only [pairFst_pair] using i.isLt⟩

attribute [local irreducible] point planAt root positiveInput positiveState input source vertex pair

theorem exists_point_sample {n : List Bool→ℕ} {t : List Bool→Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
    (original : List Bool)
    (C : Set (Zeros (polynomial (n original) (t original)))) (hC : IsClopen C)
    (x0 : Zeros (polynomial (n original) (t original))) (hx0 : x0∈C) :
    ∃ label : List Bool,∃ hv : Valid hn ht ha (pair original label),
      ∃ p : Zeros (polynomial (n original) (t original)),p∈C ∧ pointAt hn ht ha original label hv=p.val := by
  obtain ⟨labels,advice,w,label,_,_,hv,hs,hw,p,hp,hvw,hread⟩:=
    exists_valid_candidate_sample hn ht ha original C hC x0 hx0
  refine ⟨label,hv,p,hp,funext fun i=>?_⟩
  obtain ⟨j,hj,H⟩:=hread i
  exact (point_recipe hn ht ha original label hv labels advice w hs hw hvw i j hj).trans H.symm

end LeanCanny.Encoding.IntegralMixedAuxiliaryCandidate
