/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CircleSublevelLift
public import LeanCanny.Geometry.RegularPolynomialLevels
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Proper regular levels of the circle lift

The lifted energy has exactly the original critical values: its derivative
vanishes precisely when both slack coordinates and the original derivative
vanish. Nonnegative energies with compact sublevels retain that property
after lifting, giving a proper map for regular-level component transport.
-/

@[expose] public section
namespace LeanCanny.Geometry.CircleSublevelLift
open Set
open scoped RealInnerProductSpace

def energy {X : Type*} (g : X → ℝ) (p : X × ℂ) : ℝ := g p.1 + Complex.normSq p.2

section Topology
variable {X : Type*} [TopologicalSpace X]

theorem continuous_energy (g : X → ℝ) (hg : Continuous g) : Continuous (energy g) :=
  (hg.comp continuous_fst).add (Complex.continuous_normSq.comp continuous_snd)

theorem isCompact_energy_sublevel (g : X → ℝ) (hg : Continuous g)
    (hnonneg : ∀ x, 0 ≤ g x) (e : ℝ) (hbase : IsCompact (Base g e)) :
    IsCompact {p : X × ℂ | energy g p ≤ e} := by
  have hc : IsClosed {p : X × ℂ | energy g p ≤ e} := isClosed_le (continuous_energy g hg) continuous_const
  apply (hbase.prod (isCompact_closedBall (0 : ℂ) (Real.sqrt (max e 0)))).of_isClosed_subset hc
  intro p hp
  change g p.1 + Complex.normSq p.2 ≤ e at hp
  have hs : ‖p.2‖ ^ 2 ≤ max e 0 := by
    rw [← Complex.normSq_eq_norm_sq]
    linarith [hnonneg p.1, le_max_left e 0]
  have hb : ‖p.2‖ ≤ Real.sqrt (max e 0) := by
    nlinarith [Real.sq_sqrt (le_max_right e 0), Real.sqrt_nonneg (max e 0), norm_nonneg p.2]
  refine ⟨?_, ?_⟩
  · change g p.1 ≤ e
    linarith [Complex.normSq_nonneg p.2]
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hb

theorem proper_energy (g : X → ℝ) (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x)
    (hsublevel : ∀ e : ℝ, IsCompact (Base g e)) : IsProperMap (energy g) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨continuous_energy g hg, ?_⟩
  intro K hK
  obtain ⟨e, he⟩ := hK.bddAbove
  exact (isCompact_energy_sublevel g hg hnonneg e (hsublevel e)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_energy g hg)) (fun _ hp => he hp)

theorem isCompact_total (g : X → ℝ) (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x)
    (e : ℝ) (hbase : IsCompact (Base g e)) : IsCompact (Total g e) :=
  (isCompact_energy_sublevel g hg hnonneg e hbase).of_isClosed_subset
    (isClosed_eq (continuous_energy g hg) continuous_const) (fun _ hp => hp.le)

end Topology

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def derivative (D : E →L[ℝ] ℝ) (z : ℂ) : E × ℂ →L[ℝ] ℝ :=
  D.comp (ContinuousLinearMap.fst ℝ E ℂ) + 2 • (innerSL ℝ z).comp (ContinuousLinearMap.snd ℝ E ℂ)

theorem derivative_apply (D : E →L[ℝ] ℝ) (z : ℂ) (p : E × ℂ) :
    derivative D z p = D p.1 + 2 * ⟪z, p.2⟫ := by
  simp [derivative, two_smul, two_mul]

theorem hasFDerivAt_energy (g : E → ℝ) (p : E × ℂ) (hg : DifferentiableAt ℝ g p.1) :
    HasFDerivAt (energy g) (derivative (fderiv ℝ g p.1) p.2) p := by
  change HasFDerivAt (fun q : E × ℂ => g q.1 + Complex.normSq q.2) _ p
  simp only [Complex.normSq_eq_norm_sq]
  exact (hg.hasFDerivAt.comp p hasFDerivAt_fst).add hasFDerivAt_snd.norm_sq

theorem derivative_eq_zero_iff (D : E →L[ℝ] ℝ) (z : ℂ) :
    derivative D z = 0 ↔ z = 0 ∧ D = 0 := by
  constructor
  · intro h
    have hz := congrArg (fun A : E × ℂ →L[ℝ] ℝ => A (0, z)) h
    simp only [derivative_apply, map_zero, zero_add, real_inner_self_eq_norm_sq,
      zero_apply] at hz
    have hz0 : z = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖z‖]
    refine ⟨hz0, ?_⟩
    ext v
    have hv := congrArg (fun A : E × ℂ →L[ℝ] ℝ => A (v, 0)) h
    simpa only [derivative_apply, inner_zero_right, mul_zero, add_zero,
      zero_apply] using hv
  · rintro ⟨rfl, rfl⟩
    apply ContinuousLinearMap.ext
    intro p
    rw [derivative_apply]
    simp

theorem fderiv_energy_eq_zero_iff (g : E → ℝ) (p : E × ℂ) (hg : DifferentiableAt ℝ g p.1) :
    fderiv ℝ (energy g) p = 0 ↔ p.2 = 0 ∧ fderiv ℝ g p.1 = 0 := by
  rw [(hasFDerivAt_energy g p hg).fderiv, derivative_eq_zero_iff]

theorem regular_energy (g : E → ℝ) (hg : Differentiable ℝ g) (e : ℝ)
    (hregular : ∀ x, g x = e → Function.Surjective (fderiv ℝ g x))
    (p : E × ℂ) (hp : energy g p = e) : Function.Surjective (fderiv ℝ (energy g) p) := by
  apply RegularPolynomialLevels.surjective_of_ne_zero
  intro hz
  obtain ⟨hz0, hg0⟩ := (fderiv_energy_eq_zero_iff g p (hg p.1)).mp hz
  have he : g p.1 = e := by simpa only [energy, hz0, map_zero, add_zero] using hp
  obtain ⟨v, hv⟩ := hregular p.1 he 1
  rw [hg0, zero_apply] at hv
  exact zero_ne_one hv

theorem critical_value_iff (g : E → ℝ) (hg : Differentiable ℝ g) (e : ℝ) :
    (∃ p : E × ℂ, energy g p = e ∧ fderiv ℝ (energy g) p = 0) ↔
      ∃ x : E, g x = e ∧ fderiv ℝ g x = 0 := by
  constructor
  · rintro ⟨p, hp, hd⟩
    obtain ⟨hz0, hg0⟩ := (fderiv_energy_eq_zero_iff g p (hg p.1)).mp hd
    exact ⟨p.1, by simpa only [energy, hz0, map_zero, add_zero] using hp, hg0⟩
  · rintro ⟨x, hx, hd⟩
    refine ⟨(x, 0), ?_, (fderiv_energy_eq_zero_iff g (x, 0) (hg x)).mpr ⟨rfl, hd⟩⟩
    simpa only [energy, map_zero, add_zero] using hx

theorem contDiff_energy (g : E → ℝ) {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) : ContDiff ℝ n (energy g) := by
  change ContDiff ℝ n (fun q : E × ℂ => g q.1 + Complex.normSq q.2)
  simp only [Complex.normSq_eq_norm_sq]
  have hs : ContDiff ℝ n (Prod.snd : E × ℂ → ℂ) := contDiff_snd
  exact (hg.comp contDiff_fst).add (hs.norm_sq ℂ)

end Calculus
end LeanCanny.Geometry.CircleSublevelLift
