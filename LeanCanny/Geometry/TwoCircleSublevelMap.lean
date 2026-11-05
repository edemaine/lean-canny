/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CircleSublevelLevels
public import Mathlib.Analysis.Normed.Operator.Prod
/-! # A proper two-parameter map for energy and radius sublevels

The two independent circle slacks encode both inequalities. Properness uses
only compact radius sublevels, so the energy itself may have unbounded zeros.
Failure of regularity is reduced to dependence of the two old derivatives.
-/
@[expose] public section
namespace LeanCanny.Geometry.TwoCircleSublevelMap
open Set Metric
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

def energy {X : Type*} (g h : X → ℝ) (p : X × (ℂ × ℂ)) : ℝ × ℝ :=
  (g p.1 + Complex.normSq p.2.1, h p.1 + Complex.normSq p.2.2)

section Topology
variable {X : Type*} [TopologicalSpace X]

theorem continuous_energy (g h : X → ℝ) (hg : Continuous g) (hh : Continuous h) :
    Continuous (energy g h) :=
  ((hg.comp continuous_fst).add (Complex.continuous_normSq.comp (continuous_fst.comp continuous_snd))).prodMk
    ((hh.comp continuous_fst).add (Complex.continuous_normSq.comp (continuous_snd.comp continuous_snd)))

private theorem slack_bound (z : ℂ) (a : ℝ) (ha : Complex.normSq z ≤ a) :
    z ∈ closedBall 0 (Real.sqrt (max a 0)) := by
  have H : ‖z‖ ^ 2 ≤ max a 0 := by rw [← Complex.normSq_eq_norm_sq]; exact ha.trans (le_max_left _ _)
  have HN : ‖z‖ ≤ Real.sqrt (max a 0) := by
    nlinarith [Real.sq_sqrt (le_max_right a 0), Real.sqrt_nonneg (max a 0), norm_nonneg z]
  simpa only [mem_closedBall, dist_zero_right] using HN

theorem proper_energy (g h : X → ℝ) (hg : Continuous g) (hh : Continuous h)
    (hgn : ∀ x, 0 ≤ g x) (hhn : ∀ x, 0 ≤ h x)
    (hcompact : ∀ r : ℝ, IsCompact {x | h x ≤ r}) : IsProperMap (energy g h) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_energy g h hg hh, ?_⟩
  intro K hK
  obtain ⟨a,ha⟩ := (hK.image continuous_fst).bddAbove
  obtain ⟨b,hb⟩ := (hK.image continuous_snd).bddAbove
  apply ((hcompact b).prod ((isCompact_closedBall (0 : ℂ) (Real.sqrt (max a 0))).prod
    (isCompact_closedBall (0 : ℂ) (Real.sqrt (max b 0))))).of_isClosed_subset
    (hK.isClosed.preimage (continuous_energy g h hg hh))
  intro p hp
  have H1 : g p.1 + Complex.normSq p.2.1 ≤ a := ha ⟨energy g h p,hp,rfl⟩
  have H2 : h p.1 + Complex.normSq p.2.2 ≤ b := hb ⟨energy g h p,hp,rfl⟩
  refine ⟨?_,slack_bound p.2.1 a ?_,slack_bound p.2.2 b ?_⟩
  · change h p.1 ≤ b
    linarith [Complex.normSq_nonneg p.2.2]
  · linarith [hgn p.1]
  · linarith [hhn p.1]

end Topology

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def firstProjection : E × (ℂ × ℂ) →L[ℝ] E × ℂ :=
  (ContinuousLinearMap.fst ℝ E (ℂ × ℂ)).prod
    ((ContinuousLinearMap.fst ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ E (ℂ × ℂ)))
noncomputable def secondProjection : E × (ℂ × ℂ) →L[ℝ] E × ℂ :=
  (ContinuousLinearMap.fst ℝ E (ℂ × ℂ)).prod
    ((ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.snd ℝ E (ℂ × ℂ)))

noncomputable def left (D : E →L[ℝ] ℝ) (z : ℂ) : E × (ℂ × ℂ) →L[ℝ] ℝ :=
  (CircleSublevelLift.derivative D z).comp firstProjection
noncomputable def right (D : E →L[ℝ] ℝ) (w : ℂ) : E × (ℂ × ℂ) →L[ℝ] ℝ :=
  (CircleSublevelLift.derivative D w).comp secondProjection
noncomputable def derivative (Dg Dh : E →L[ℝ] ℝ) (z w : ℂ) : E × (ℂ × ℂ) →L[ℝ] ℝ × ℝ :=
  (left Dg z).prod (right Dh w)

theorem left_apply (D : E →L[ℝ] ℝ) (z : ℂ) (p : E × (ℂ × ℂ)) :
    left D z p = D p.1 + 2 * ⟪z, p.2.1⟫ := by
  change CircleSublevelLift.derivative D z (p.1,p.2.1) = _
  exact CircleSublevelLift.derivative_apply D z (p.1,p.2.1)
theorem right_apply (D : E →L[ℝ] ℝ) (w : ℂ) (p : E × (ℂ × ℂ)) :
    right D w p = D p.1 + 2 * ⟪w, p.2.2⟫ := by
  change CircleSublevelLift.derivative D w (p.1,p.2.2) = _
  exact CircleSublevelLift.derivative_apply D w (p.1,p.2.2)

theorem hasFDerivAt_energy (g h : E → ℝ) (p : E × (ℂ × ℂ))
    (hg : DifferentiableAt ℝ g p.1) (hh : DifferentiableAt ℝ h p.1) :
    HasFDerivAt (energy g h) (derivative (fderiv ℝ g p.1) (fderiv ℝ h p.1) p.2.1 p.2.2) p := by
  have L := (CircleSublevelLift.hasFDerivAt_energy g (p.1,p.2.1) hg).comp p firstProjection.hasFDerivAt
  have R := (CircleSublevelLift.hasFDerivAt_energy h (p.1,p.2.2) hh).comp p secondProjection.hasFDerivAt
  exact L.prodMk R

theorem contDiff_energy (g h : E → ℝ) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 1 (energy g h) :=
  ((CircleSublevelLift.contDiff_energy g hg).comp firstProjection.contDiff).prodMk
    ((CircleSublevelLift.contDiff_energy h hh).comp secondProjection.contDiff)

private theorem pair_surjective (A B : E →L[ℝ] ℝ) (hA : Function.Surjective A)
    (hB : ∀ c : ℝ, B ≠ c • A) : Function.Surjective (A.prod B) := by
  classical
  obtain ⟨u,hu⟩ := hA 1
  have HV : ∃ v : E, A v = 0 ∧ B v ≠ 0 := by
    by_contra H
    have HB : ∀ v : E, A v = 0 → B v = 0 := by
      intro v hv
      by_contra h
      exact H ⟨v,hv,h⟩
    apply hB (B u)
    ext v
    have H0 := HB (v - A v • u) (by simp only [map_sub,map_smul,smul_eq_mul,hu,mul_one,sub_self])
    simp only [map_sub,map_smul,smul_eq_mul] at H0
    change B v = B u * A v
    nlinarith
  obtain ⟨v,hv,hBv⟩ := HV
  rintro ⟨a,b⟩
  refine ⟨a • u + ((b - a * B u) / B v) • v, Prod.ext ?_ ?_⟩
  · change A (a • u + ((b - a * B u) / B v) • v) = a
    simp only [map_add, map_smul, smul_eq_mul, hu, hv,
      mul_one,mul_zero,add_zero]
  · change B (a • u + ((b - a * B u) / B v) • v) = b
    simp only [map_add, map_smul, smul_eq_mul]
    rw [div_mul_cancel₀ _ hBv]
    ring

theorem derivative_surjective (Dg Dh : E →L[ℝ] ℝ) (z w : ℂ)
    (hfirst : Function.Surjective (CircleSublevelLift.derivative Dg z))
    (hsecond : w = 0 → Dh ≠ 0)
    (hboundary : z = 0 → w = 0 → ∀ c : ℝ, Dh ≠ c • Dg) :
    Function.Surjective (derivative Dg Dh z w) := by
  have HL : Function.Surjective (left Dg z) := by
    intro a
    obtain ⟨⟨v,t⟩,hv⟩ := hfirst a
    exact ⟨(v,(t,0)),by simpa only [left_apply, CircleSublevelLift.derivative_apply] using hv⟩
  apply pair_surjective (left Dg z) (right Dh w) HL
  intro c HE
  have HW : w = 0 := by
    have H := congrArg (fun D : E × (ℂ × ℂ) →L[ℝ] ℝ => D (0,(0,w))) HE
    simp only [right_apply,left_apply,map_zero,zero_add,inner_zero_right,mul_zero,
      smul_apply,smul_eq_mul,real_inner_self_eq_norm_sq] at H
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖w‖]
  have HC : c ≠ 0 := by
    intro hc
    apply hsecond HW
    ext v
    have H := congrArg (fun D : E × (ℂ × ℂ) →L[ℝ] ℝ => D (v,(0,0))) HE
    simpa only [right_apply,left_apply,inner_zero_right,mul_zero,add_zero,
      smul_apply,smul_eq_mul,hc,zero_mul,zero_apply] using H
  have HZ : z = 0 := by
    have H := congrArg (fun D : E × (ℂ × ℂ) →L[ℝ] ℝ => D (0,(z,0))) HE
    simp only [right_apply,left_apply,map_zero,zero_add,inner_zero_right,mul_zero,
      smul_apply,smul_eq_mul,real_inner_self_eq_norm_sq] at H
    have HN : ‖z‖ ^ 2 = 0 := by
      have H2 := (mul_eq_zero.mp H.symm).resolve_left HC
      nlinarith
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp HN)
  apply hboundary HZ HW c
  ext v
  have H := congrArg (fun D : E × (ℂ × ℂ) →L[ℝ] ℝ => D (v,(0,0))) HE
  simpa only [right_apply,left_apply,inner_zero_right,mul_zero,add_zero,
    smul_apply,smul_eq_mul] using H

end Calculus
end LeanCanny.Geometry.TwoCircleSublevelMap
