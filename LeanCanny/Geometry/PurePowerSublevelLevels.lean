/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.PurePowerSublevelLift
public import LeanCanny.Geometry.CircleSublevelLevels

/-! # Proper regular pure-power sublevel lifts

The two even-power slack derivatives vanish together precisely at zero.
Hence the lifted and original energies have the same critical values. For
twice an odd degree, the coordinate homeomorphism also transfers compactness
and properness from the circle lift while preserving its components.
-/

@[expose] public section
namespace LeanCanny.Geometry.PurePowerSublevelLift
open Set

def energy {X : Type*} (m : ℕ) (g : X → ℝ) (p : X × ℂ) : ℝ := g p.1 + penalty m p.2

section Topology
variable {X : Type*} [TopologicalSpace X]

theorem energy_eq_comp (m : ℕ) (hm : Odd m) (g : X → ℝ) :
    energy m g = CircleSublevelLift.energy g ∘ spaceMap m hm := by
  funext p
  change g p.1 + penalty m p.2 = g p.1 + Complex.normSq (powerMap m hm p.2)
  rw [normSq_powerMap]

theorem proper_energy (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x)
    (hsublevel : ∀ e : ℝ, IsCompact (CircleSublevelLift.Base g e)) : IsProperMap (energy m g) := by
  rw [energy_eq_comp m hm g]
  exact (CircleSublevelLift.proper_energy g hg hnonneg hsublevel).comp (spaceMap m hm).isProperMap

theorem isCompact_total (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (hnonneg : ∀ x, 0 ≤ g x)
    (e : ℝ) (hbase : IsCompact (CircleSublevelLift.Base g e)) : IsCompact (Total m g e) := by
  rw [total_eq_preimage m hm g e]
  exact (spaceMap m hm).isCompact_preimage.mpr (CircleSublevelLift.isCompact_total g hg hnonneg e hbase)

end Topology

section Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def derivative (m : ℕ) (D : E →L[ℝ] ℝ) (z : ℂ) : E × ℂ →L[ℝ] ℝ :=
  D.comp (ContinuousLinearMap.fst ℝ E ℂ) +
    (((2 * m) • z.re ^ (2 * m - 1)) • (Complex.reCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)) +
      ((2 * m) • z.im ^ (2 * m - 1)) • (Complex.imCLM.comp (ContinuousLinearMap.snd ℝ E ℂ)))

theorem derivative_apply (m : ℕ) (D : E →L[ℝ] ℝ) (z : ℂ) (p : E × ℂ) :
    derivative m D z p = D p.1 +
      ((2 * m : ℕ) : ℝ) * z.re ^ (2 * m - 1) * p.2.re +
      ((2 * m : ℕ) : ℝ) * z.im ^ (2 * m - 1) * p.2.im := by
  simp only [derivative, add_apply, ContinuousLinearMap.comp_apply, smul_apply]
  change D p.1 + (((2 * m) • z.re ^ (2 * m - 1)) • p.2.re +
    ((2 * m) • z.im ^ (2 * m - 1)) • p.2.im) = _
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

theorem hasFDerivAt_energy (m : ℕ) (g : E → ℝ) (p : E × ℂ) (hg : DifferentiableAt ℝ g p.1) :
    HasFDerivAt (energy m g) (derivative m (fderiv ℝ g p.1) p.2) p := by
  have hr := Complex.reCLM.hasFDerivAt.comp p hasFDerivAt_snd
  have hi := Complex.imCLM.hasFDerivAt.comp p hasFDerivAt_snd
  exact (hg.hasFDerivAt.comp p hasFDerivAt_fst).add ((hr.pow (2 * m)).add (hi.pow (2 * m)))

theorem derivative_eq_zero_iff (m : ℕ) (hm : 0 < m) (D : E →L[ℝ] ℝ) (z : ℂ) :
    derivative m D z = 0 ↔ z = 0 ∧ D = 0 := by
  have hN : (((2 * m : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (show 2 * m ≠ 0 by omega)
  constructor
  · intro h
    have hr := congrArg (fun A : E × ℂ →L[ℝ] ℝ => A (0, 1)) h
    have hi := congrArg (fun A : E × ℂ →L[ℝ] ℝ => A (0, Complex.I)) h
    simp only [derivative_apply, map_zero, Complex.one_re, mul_one, Complex.one_im, mul_zero,
      add_zero, zero_add, zero_apply] at hr
    simp only [derivative_apply, map_zero, Complex.I_re, mul_zero, Complex.I_im, mul_one,
      zero_add, zero_apply] at hi
    have hz0 : z = 0 := Complex.ext
      (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hr).resolve_left hN))
      (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hi).resolve_left hN))
    refine ⟨hz0, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    have hv := congrArg (fun A : E × ℂ →L[ℝ] ℝ => A (v, 0)) h
    simpa only [derivative_apply, Complex.zero_re, Complex.zero_im, mul_zero, add_zero, zero_apply] using hv
  · rintro ⟨rfl, rfl⟩
    apply ContinuousLinearMap.ext
    intro p
    rw [derivative_apply]
    simp only [zero_apply, Complex.zero_re, Complex.zero_im, zero_pow (by omega : 2 * m - 1 ≠ 0),
      mul_zero, zero_mul, zero_add]

theorem fderiv_energy_eq_zero_iff (m : ℕ) (hm : 0 < m) (g : E → ℝ) (p : E × ℂ)
    (hg : DifferentiableAt ℝ g p.1) :
    fderiv ℝ (energy m g) p = 0 ↔ p.2 = 0 ∧ fderiv ℝ g p.1 = 0 := by
  rw [(hasFDerivAt_energy m g p hg).fderiv, derivative_eq_zero_iff m hm]

theorem regular_energy (m : ℕ) (hm : 0 < m) (g : E → ℝ) (hg : Differentiable ℝ g) (e : ℝ)
    (hregular : ∀ x, g x = e → Function.Surjective (fderiv ℝ g x))
    (p : E × ℂ) (hp : energy m g p = e) : Function.Surjective (fderiv ℝ (energy m g) p) := by
  apply RegularPolynomialLevels.surjective_of_ne_zero
  intro hz
  obtain ⟨hz0, hg0⟩ := (fderiv_energy_eq_zero_iff m hm g p (hg p.1)).mp hz
  have he : g p.1 = e := by
    simpa only [energy, penalty, hz0, Complex.zero_re, Complex.zero_im, zero_pow (by omega : 2 * m ≠ 0),
      zero_add, add_zero] using hp
  obtain ⟨v, hv⟩ := hregular p.1 he 1
  rw [hg0, zero_apply] at hv
  exact zero_ne_one hv

theorem critical_value_iff (m : ℕ) (hm : 0 < m) (g : E → ℝ) (hg : Differentiable ℝ g) (e : ℝ) :
    (∃ p : E × ℂ, energy m g p = e ∧ fderiv ℝ (energy m g) p = 0) ↔
      ∃ x : E, g x = e ∧ fderiv ℝ g x = 0 := by
  constructor
  · rintro ⟨p, hp, hd⟩
    obtain ⟨hz0, hg0⟩ := (fderiv_energy_eq_zero_iff m hm g p (hg p.1)).mp hd
    refine ⟨p.1, ?_, hg0⟩
    simpa only [energy, penalty, hz0, Complex.zero_re, Complex.zero_im, zero_pow (by omega : 2 * m ≠ 0),
      zero_add, add_zero] using hp
  · rintro ⟨x, hx, hd⟩
    refine ⟨(x, 0), ?_, (fderiv_energy_eq_zero_iff m hm g (x, 0) (hg x)).mpr ⟨rfl, hd⟩⟩
    simpa only [energy, penalty, Complex.zero_re, Complex.zero_im, zero_pow (by omega : 2 * m ≠ 0),
      zero_add, add_zero] using hx

theorem contDiff_energy (m : ℕ) (g : E → ℝ) {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (energy m g) := by
  have hr : ContDiff ℝ n (fun p : E × ℂ => p.2.re) := Complex.reCLM.contDiff.comp contDiff_snd
  have hi : ContDiff ℝ n (fun p : E × ℂ => p.2.im) := Complex.imCLM.contDiff.comp contDiff_snd
  exact (hg.comp contDiff_fst).add ((hr.pow (2 * m)).add (hi.pow (2 * m)))

end Calculus
end LeanCanny.Geometry.PurePowerSublevelLift
