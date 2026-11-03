/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointMidpointSweepAnchor
public import LeanCanny.Geometry.IntegralMixedJointMidpointWitness
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
/-! # The scale-two joint anchor selects a closed physical branch

Every endpoint remains a physical critical point in its actual frozen
fiber, including singular endpoint fibers. Coordinates are explicitly
returned from frozen-first order to the original spatial order.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem selected_point_endpoint (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (v : Fin (n+1)→ℝ)
    (hv : v∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t) :
    let point:=v∘(FrozenCoordinateOrdering.permutation (line F h).frozen).symm
    point∈slice P F values ∧ point h=t ∧
      ∀i,i∉(line F h).frozen→i≠g→
        (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) point=0 :=by
  let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
  have HS:=physical_mem_shiftedSlice x hm φ (line F h) h (Finset.mem_insert_self h F.frozen)
    g hg values H t v hv
  rw [line_slice P F h hh HF values] at HS
  refine ⟨HS.1,HS.2,?_⟩
  apply selected_physical_gradients x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg t
  simpa only [e,cutSource,cutRule,Function.comp_def,Equiv.symm_apply_apply] using hv

theorem joint_midpoint_block_branch [Fintype κ]
    (x : State P S B m ι) (hm : m≤S) (atAnchor : State P S B (m+2) κ) (ha : m+2≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (HF : FreeNormal F) (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b anchor : ℝ) (hab : a<b)
    (z : ((κ⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit)→ℝ)
    (hz : ∀i,((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0)
    (ψ : (criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalarPrefix.basis.generator i)=
      z ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalar i)^
        UniformIntegralPowerSchedule.weights S (2^B) (m+3) i)
    (HN : ∀i,ψ ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).bank.numerator i)/
      ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).bank.denominator i:ℝ)=
        (Fin.cons anchor (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i)
    (cuts : IntegralMixedRelativeCuts.Choices (cutSource x F h) hm (cutRule x F h g hg) φ)
    (havoid : ∀t∈Ioo a b,t∉IntegralMixedSelectedCriticalCuts.bad (cutSource x F h) hm (cutRule x F h g hg) φ cuts) :
    let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
    let point:=IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m+2) z
    let mid:ℝ:=(a+b)/2
    let HR:=midpoint_block_anchors_sweep x hm atAnchor ha φ F HF HP HA h g j hfirst hh hg hj values H a b anchor z hz ψ hψ HN
    ∃f : ℝ→Fin (n+1)→ℝ,∃code : List Bool,
      code=IntegralMixedFrozenFrameSectionCode.word (cutSource x F h) hm (cutRule x F h g hg) φ mid ⟨point∘e,HR⟩ ∧
      code.length=(n+1)*B ∧ f mid=point∘e ∧ ContinuousOn f (Icc a b) ∧
      (∀t,t∈Icc a b→f t∈IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t) ∧
      (∀t,t∈Icc a b→
        (f t∘e.symm)∈slice P F values ∧ (f t∘e.symm) h=t ∧
          ∀i,i∉(line F h).frozen→i≠g→
            (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
              (Int.castRingHom ℝ) (f t∘e.symm)=0) ∧
      ∀endpoint∈Icc a b,∀v : Fin (n+1)→ℝ,
        IntegralMixedSelectedCoordinateEndpoint.Frozen (cutSource x F h) hm (cutRule x F h g hg) φ endpoint v→
          ((∀i,IntegralMixedSelectedCoordinateEndpoint.Near (cutSource x F h) hm (cutRule x F h g hg) φ a b endpoint i
            (IntegralMixedSelectedCoordinateEndpoint.digit B code i)
            (v (ClearedCoordinateCritical.freeIndex (cutRule x F h g hg).critical.offset.val (fit (cutRule x F h g hg)).le i)))↔
              f endpoint=v) :=by
  let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
  let mid : Ioo a b:=⟨(a+b)/2,by constructor <;> linarith⟩
  have HR:=midpoint_block_anchors_sweep x hm atAnchor ha φ F HF HP HA h g j hfirst hh hg hj values H a b anchor z hz ψ hψ HN
  let p : IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ mid.val:=
    ⟨IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m+2) z∘e,HR⟩
  obtain ⟨curve,HCrit,Hanchor,Hcont,_,code,_,Hlen,Hword,Hend⟩:=
    IntegralMixedSelectedCoordinateEndpoint.exists_matched_codes (cutSource x F h) hm (cutRule x F h g hg) φ cuts a b mid havoid
  have HE : (⟨curve p mid.val,HCrit p mid.val (Ioo_subset_Icc_self mid.property)⟩ :
      IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ mid.val)=p:=
    Subtype.ext (Hanchor p)
  have HW:=Hword p mid
  rw [HE] at HW
  refine ⟨curve p,code p,HW.symm,Hlen p,Hanchor p,Hcont p,HCrit p,?_,Hend p⟩
  intro t ht
  exact selected_point_endpoint x hm φ F h hh HF g hg values H t (curve p t) (HCrit p t ht)

end LeanCanny.Geometry.IntegralMixedFrozenFrame
