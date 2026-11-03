/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameMidpointAnchor
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
/-! # Literal advanced critical points anchor the selected slab branches

The anchor is read from the actual point rule and the retained midpoint
bank. The ordinal code is its literal all-real coordinate-root word.
Selected cuts and slab avoidance remain explicit geometric inputs.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem advance_point_branch (x : State P S B m ι) (hm : m≤S)
    (next : State P S B (m+1) κ) (hnm : m+1≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : next.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (j : Fin (n+1)) (hj : j∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    {left right : ℝ} (midpoint : Ioo left right)
    (HN : ∀i,ψ (next.bank.numerator i)/(next.bank.denominator i:ℝ)=(Fin.cons midpoint.val values : Fin (m+1)→ℝ) i)
    (a : Fin (n+1)→ℝ)
    (HA : IntegralMixedCriticalReadback.CriticalPoint
      (IntegralMixedCoordinateRename.state next (FrozenCoordinateOrdering.permutation (advance F h).frozen)) hnm
      (pointRule (advance F h) g hg j hj) ψ a)
    (cuts : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (havoid : ∀t∈Ioo left right,t∉IntegralMixedSelectedCriticalCuts.bad (cutSource x F h) hm (cutRule x F h g hg) φ cuts) :
    let HR:=advance_point_anchors_sweep x hm next hnm φ ψ F h hh HF g hg j hj values H midpoint.val HN a HA
    ∃f : ℝ→Fin (n+1)→ℝ,∃code : List Bool,
      code=IntegralMixedFrozenFrameSectionCode.word (cutSource x F h) hm (cutRule x F h g hg) φ midpoint.val ⟨a,HR⟩ ∧
      code.length=(n+1)*B ∧ f midpoint.val=a ∧ ContinuousOn f (Icc left right) ∧
      (∀t,t∈Icc left right→f t∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t) ∧
      ∀endpoint∈Icc left right,∀y : Fin (n+1)→ℝ,
        IntegralMixedSelectedCoordinateEndpoint.Frozen (cutSource x F h) hm (cutRule x F h g hg) φ endpoint y→
        ((∀i,IntegralMixedSelectedCoordinateEndpoint.Near (cutSource x F h) hm (cutRule x F h g hg) φ left right endpoint i
          (IntegralMixedSelectedCoordinateEndpoint.digit B code i)
          (y (ClearedCoordinateCritical.freeIndex (cutRule x F h g hg).critical.offset.val (fit (cutRule x F h g hg)).le i)))↔
          f endpoint=y) :=by
  let HR:=advance_point_anchors_sweep x hm next hnm φ ψ F h hh HF g hg j hj values H midpoint.val HN a HA
  obtain ⟨curve,HCrit,Hanchor,Hcont,_,code,_,Hlen,Hword,Hend⟩:=
    IntegralMixedSelectedCoordinateEndpoint.exists_matched_codes (cutSource x F h) hm (cutRule x F h g hg) φ cuts left right midpoint havoid
  let p : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ midpoint.val:=⟨a,HR⟩
  have HE : (⟨curve p midpoint.val,HCrit p midpoint.val (Ioo_subset_Icc_self midpoint.property)⟩ :
      IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ midpoint.val)=p:=
    Subtype.ext (Hanchor p)
  have HW:=Hword p midpoint
  rw [HE] at HW
  exact ⟨curve p,code p,HW.symm,Hlen p,Hanchor p,Hcont p,HCrit p,Hend p⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
