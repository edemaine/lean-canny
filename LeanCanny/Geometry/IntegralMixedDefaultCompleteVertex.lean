/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex
public import LeanCanny.Geometry.CanonicalAuxiliaryZeroReadback

/-! # Default-extended original samples have complete native vertices

The same interpreting hom supplies all coordinates at once. After integer X
is appended, original coordinate i is the actual bank point at index n-i.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical

theorem default_complete_vertex {a n S B : ℕ} {P : SpatialSource a}
    (initial : State P S B 0 (Fin 0)) (cs : List (Instruction a B))
    (hcs : cs.length≤S+1) (hm : cs.length≤S)
    (hc : ∀ c∈cs,c.command.isCritical=false) (p : Fin n→ℝ)
    (hp : OriginalRealization (run initial cs hcs) p)
    (F : SquareSampleInput.Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (hcount : F.count u=cs.length+1)
    (hrows : HEq (F.system u)
      (run initial (zeroInstruction initial::cs)
        (by simp only [List.length_cons]; omega)).sampler.scalarPrefix.rows) :
    let next:=run initial (zeroInstruction initial::cs)
      (by simp only [List.length_cons]; omega)
    ∃ w : List Bool, ∃ hw : SquareSampleCompleteVertices.Valid F u w,
      w.length=SquareSampleCompleteVertices.width F u ∧
      (IntegralMixedCanonicalCompleteVertex.tuple F u w hw hcount) 0=0 ∧
      ∀ i : Fin n,∃ j : Fin (cs.length+1),j.val=n-i.val ∧
        p i=IntegralMixedCanonicalBankPoint.point next
          (IntegralMixedCanonicalCompleteVertex.tuple F u w hw hcount) j := by
  obtain ⟨z,φ,hz,hzero,hφ,hread⟩:=canonical_zero_readback initial cs hcs hm hc p hp
  let next:=run initial (zeroInstruction initial::cs)
    (by simp only [List.length_cons]; omega)
  have H0 : Canonical initial := fun i=>Fin.elim0 i
  have HN : Canonical next := run_canonical initial H0 _ _
  obtain ⟨w,hw,hlen,htuple,hquot⟩:=IntegralMixedCanonicalCompleteVertex.exists_vertex
    next HN F hF u hcount hrows z hz φ hφ
  refine ⟨w,hw,hlen,?_,?_⟩
  · rw [htuple]
    exact hzero
  · intro i
    obtain ⟨j,hj,hvalue⟩:=hread i
    exact ⟨j,hj,hvalue.trans (hquot j)⟩

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
