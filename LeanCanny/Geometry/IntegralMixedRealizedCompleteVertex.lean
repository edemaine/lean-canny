/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedCanonicalCompleteVertex
public import LeanCanny.Algebra.IntegralMixedIntegerRealization
public import LeanCanny.Algebra.IntegralHistoryScalarOnly
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation

/-! # A realized scalar-only bank has one complete vertex retaining every value -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedRealizedCompleteVertex
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_vertex {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (H : Canonical x) (hs : IntegralHistorySampler.ScalarOnly x.sampler)
    (F : SquareSampleInput.Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (hm : F.count u=m) (hr : HEq (F.system u) x.sampler.scalarPrefix.rows)
    (values : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes x values) :
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid F u w,
      w.length=SquareSampleCompleteVertices.width F u ∧ ∀i : Fin m,
        IntegralMixedCanonicalBankPoint.point x (IntegralMixedCanonicalCompleteVertex.tuple F u w hw hm) i=values i.val := by
  obtain ⟨y,φ,hy,hφ,hvalues⟩:=hv
  let z:=y∘x.sampler.scalar
  have HE : z∘hs.equiv.symm=y := by
    funext j
    exact congrArg y (hs.equiv.apply_symm_apply j)
  have HZ : ∀i,(x.sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0 := by
    apply (hs.roots_iff z).mpr
    rw [HE]
    exact hy
  obtain ⟨w,hw,hlen,_,hread⟩:=IntegralMixedCanonicalCompleteVertex.exists_vertex x H F hF u hm hr z HZ φ hφ
  exact ⟨w,hw,hlen,fun i=>(hread i).symm.trans (hvalues i)⟩

theorem extend_tuple (F : SquareSampleInput.Inputs) (u w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid F u w) {m : ℕ} (hm : F.count u=m) :
    IntegralMixedFramedBankObservation.extend (IntegralMixedCanonicalCompleteVertex.tuple F u w hw hm)=
      IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate F u w hw).val := by
  cases hm
  rfl

theorem exists_observed {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (H : Canonical x) (hs : IntegralHistorySampler.ScalarOnly x.sampler)
    (F : SquareSampleInput.Inputs) (hF : SquareSampleComplete.Complete F) (u : List Bool)
    (hm : F.count u=m) (hr : HEq (F.system u) x.sampler.scalarPrefix.rows)
    (values : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes x values) :
    ∃w : List Bool,∃hw : SquareSampleCompleteVertices.Valid F u w,
      w.length=SquareSampleCompleteVertices.width F u ∧ ∀i<m,
        (IntegralMixedFramedBankObservation.ofState x).point
          (IntegralMixedFramedBankObservation.extend (SquareSampleCompleteVertices.candidate F u w hw).val) i=values i := by
  obtain ⟨w,hw,hlen,hvalues⟩:=exists_vertex x H hs F hF u hm hr values hv
  refine ⟨w,hw,hlen,fun i hi=>?_⟩
  have HP:=IntegralMixedFramedBankObservation.point_ofState x
    (IntegralMixedCanonicalCompleteVertex.tuple F u w hw hm) ⟨i,hi⟩
  rw [extend_tuple] at HP
  exact HP.trans (hvalues ⟨i,hi⟩)

end LeanCanny.Geometry.IntegralMixedRealizedCompleteVertex
