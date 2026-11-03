/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointMidpointSound
public import LeanCanny.Geometry.IntegralMixedPrefixPointReadback
public import LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber
/-! # A literal scale-two midpoint block anchors the earlier selected sweep

The midpoint is the sum of two retained references divided by two. The
new head is an anchor scalar, never a presumed retained midpoint value.
Each state's actual clearing denominator is cancelled independently.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι κ : Type}

theorem source_gradients_anchor_sweep (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (point : Fin (n+1)→ℝ)
    (hp : point∈slice P F values) (ht : point h=t)
    (hgrad : ∀i,i∉(line F h).frozen→i≠g→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) point=0) :
    point∘FrozenCoordinateOrdering.permutation (line F h).frozen∈
      IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ t :=by
  let e:=FrozenCoordinateOrdering.permutation (line F h).frozen
  let r:=cutRule x F h g hg
  have HS : point∈slice P (coarse (line F h) h) values∩{y | projection (line F h) values h y=t}:=by
    rw [coarse_line F h hh]
    exact ⟨hp,(line_projection F h (HF h hh) values point).trans ht⟩
  have HW : point∘e∈sweepSlice x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg t :=by
    rw [sweepSlice_eq x hm φ (line F h) h (Finset.mem_insert_self h F.frozen) g hg values H t]
    simpa only [e,Set.mem_ofPred_eq,Function.comp_def,Equiv.apply_symm_apply] using HS
  refine ⟨HW.2,fun k=>?_⟩
  unfold IntegralMixedSweepRows.integerRow
  split_ifs with hk
  · exact HW.1
  · let i:=ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le k
    have HI : e i∉(line F h).frozen:=by
      intro hi
      have HE:=(FrozenCoordinateOrdering.permutation_mem_iff (line F h).frozen i).mp hi
      change (line F h).frozen.card+k.val<(line F h).frozen.card at HE
      omega
    have Hne : e i≠g:=by
      intro HE
      have HO:=objective_physical x (line F h) h (Finset.mem_insert_self h F.frozen) g hg
      have HV:=congrArg Fin.val (e.injective (HE.trans HO.symm))
      apply hk
      apply Fin.ext
      change (line F h).frozen.card+k.val=(line F h).frozen.card+(objective r).val at HV
      exact Nat.add_left_cancel HV
    rw [IntegralMixedCoordinateRename.derivative_eval P e i (point∘e)]
    have HE : (point∘e)∘e.symm=point:=by
      funext j
      exact congrArg point (e.apply_symm_apply j)
    rw [HE]
    exact hgrad (e i) HI Hne

theorem midpoint_point_anchors_sweep (x : State P S B m ι) (hm : m≤S)
    (atAnchor : State P S B (m+2) κ) (ha : m+2≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : atAnchor.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (HF : FreeNormal F) (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b : ℝ)
    (HN : ∀i,ψ (atAnchor.bank.numerator i)/(atAnchor.bank.denominator i:ℝ)=
      (Fin.cons b (Fin.cons a values) : Fin (m+2)→ℝ) i)
    (point : Fin (n+1)→ℝ)
    (HC : IntegralMixedCriticalReadback.CriticalPoint atAnchor ha (midpointData HA h g j hg hj).rule ψ point) :
    point∘FrozenCoordinateOrdering.permutation (line F h).frozen∈
      IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ ((a+b)/2) :=by
  have HM:=HP.midpointFrame HA h hfirst hh
  have HR : (midpointData HA h g j hg hj).rule=pointRule (midpointFrame HA h) g hg j hj:=by
    exact originalPointData_rule _ _ _ _ _ _ _
  rw [HR] at HC
  obtain ⟨HS,HG⟩:=HM.point_readback atAnchor ha ψ (midpointFrame HA h) g j hg hj
    (Fin.cons b (Fin.cons a values)) HN point HC
  have HE:=(Set.ext_iff.mp (midpointFrame_slice HA h hh values a b) point).mp HS
  exact source_gradients_anchor_sweep x hm φ F h hh HF g hg values H ((a+b)/2) point HE.1 HE.2 HG

theorem midpoint_block_anchors_sweep [Fintype κ]
    (x : State P S B m ι) (hm : m≤S) (atAnchor : State P S B (m+2) κ) (ha : m+2≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (F : Frame n) (HF : FreeNormal F) (HP : PrefixFrozen F) (HA : AtomicRows F m)
    (h g j : Fin (n+1)) (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (values : Fin m→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (a b anchor : ℝ)
    (z : ((κ⊕FlatAffineCriticalStage.Variables (n+1))⊕Unit)→ℝ)
    (hz : ∀i,((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0)
    (ψ : (criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hψ : ∀i,ψ ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalarPrefix.basis.generator i)=
      z ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).sampler.scalar i)^
        UniformIntegralPowerSchedule.weights S (2^B) (m+3) i)
    (HN : ∀i,ψ ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).bank.numerator i)/
      ((criticalStep atAnchor ha (midpointData HA h g j hg hj).rule).bank.denominator i:ℝ)=
        (Fin.cons anchor (Fin.cons b (Fin.cons a values)) : Fin (m+3)→ℝ) i) :
    IntegralMixedCriticalReadback.point (S:=S) (B:=B) (m:=m+2) z∘
        FrozenCoordinateOrdering.permutation (line F h).frozen∈
      IntegralMixedSelectedPhysicalFiber.physical (cutSource x F h) hm (cutRule x F h g hg) φ ((a+b)/2) :=by
  let χ:=ψ.comp (AdjoinRoot.ofAlgHom ℤ _)
  have HG (i : Fin (m+2)) : χ (atAnchor.sampler.scalarPrefix.basis.generator i)=
      z (Sum.inl (Sum.inl (atAnchor.sampler.scalar i)))^UniformIntegralPowerSchedule.weights S (2^B) (m+2) i :=by
    have HE:=hψ i.succ
    change ψ (AdjoinRoot.of _ (atAnchor.sampler.scalarPrefix.basis.generator i))=
      z (Sum.inl (Sum.inl (atAnchor.sampler.scalar i)))^UniformIntegralPowerSchedule.weights S (2^B) (m+3) i.succ at HE
    rw [UniformIntegralPowerSchedule.old] at HE
    exact HE
  have HV (i : Fin (m+2)) : χ (atAnchor.bank.numerator i)/(atAnchor.bank.denominator i:ℝ)=
      (Fin.cons b (Fin.cons a values) : Fin (m+2)→ℝ) i:=HN i.succ
  have HC:=IntegralMixedCriticalReadback.roots_for_interpretation atAnchor ha
    (midpointData HA h g j hg hj).rule z hz χ HG
  exact midpoint_point_anchors_sweep x hm atAnchor ha φ χ F HF HP HA h g j hfirst hh hg hj values H a b HV _ HC

end LeanCanny.Geometry.IntegralMixedFrozenFrame
