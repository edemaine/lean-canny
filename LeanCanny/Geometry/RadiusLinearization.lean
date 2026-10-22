/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AdditiveSubmersion
public import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Linearization of a radius-constrained additive family

Keeping the radius parameter free gives a surjective derivative at every
nonzero radius. At fixed radius, surjectivity is equivalent to nonvanishing of
the radius derivative composed with the original spatial derivative.
-/

@[expose] public section

namespace LeanCanny.Geometry.RadiusLinearization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def fixedDerivative (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) : E × F →L[ℝ] F × ℝ :=
  (AdditiveSubmersion.derivative D).prod (L.comp (ContinuousLinearMap.snd ℝ E F))

theorem fixedDerivative_apply (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) (w : E × F) :
    fixedDerivative D L w = (D w.1 + w.2, L w.2) := by
  simp [fixedDerivative, AdditiveSubmersion.derivative]

noncomputable def jointDerivative (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) (delta : ℝ) :
    (E × F) × ℝ →L[ℝ] F × ℝ :=
  ((AdditiveSubmersion.derivative D).comp (ContinuousLinearMap.fst ℝ (E × F) ℝ)).prod
    ((L.comp (ContinuousLinearMap.snd ℝ E F)).comp (ContinuousLinearMap.fst ℝ (E × F) ℝ) -
      (2 * delta) • ContinuousLinearMap.snd ℝ (E × F) ℝ)

theorem jointDerivative_apply (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) (delta : ℝ) (w : (E × F) × ℝ) :
    jointDerivative D L delta w = (D w.1.1 + w.1.2, L w.1.2 - 2 * delta * w.2) := by
  simp [jointDerivative, AdditiveSubmersion.derivative]

theorem jointDerivative_surjective (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) (delta : ℝ) (hd : delta ≠ 0) :
    Function.Surjective (jointDerivative D L delta) := by
  intro b
  refine ⟨((0, b.1), (L b.1 - b.2) / (2 * delta)), ?_⟩
  rw [jointDerivative_apply]
  simp only [map_zero, zero_add]
  apply Prod.ext
  · rfl
  · dsimp
    field_simp [hd]
    ring

theorem fixedDerivative_surjective_iff (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) :
    Function.Surjective (fixedDerivative D L) ↔ L.comp D ≠ 0 := by
  constructor
  · intro h hz
    obtain ⟨⟨u, v⟩, huv⟩ := h (0, 1)
    rw [fixedDerivative_apply] at huv
    have h1 : D u + v = 0 := congrArg Prod.fst huv
    have h2 : L v = 1 := congrArg Prod.snd huv
    have h0 : L (D u) = 0 := congrArg (fun M : E →L[ℝ] ℝ => M u) hz
    have he := congrArg L h1
    rw [map_add, h0, h2, map_zero, zero_add] at he
    exact one_ne_zero he
  · intro h
    have hex : ∃ u, (L.comp D) u ≠ 0 := by
      by_contra! hu
      exact h (ContinuousLinearMap.ext fun u => hu u)
    obtain ⟨u, hu⟩ := hex
    change L (D u) ≠ 0 at hu
    intro b
    let t : ℝ := (L b.1 - b.2) / L (D u)
    refine ⟨(t • u, b.1 - D (t • u)), ?_⟩
    rw [fixedDerivative_apply]
    apply Prod.ext
    · simp only [add_sub_cancel]
    · simp only [map_sub, map_smul, smul_eq_mul]
      dsimp [t]
      field_simp [hu]
      ring

noncomputable def fixedMap (f : E → F) (r : F → ℝ) (delta : ℝ) (z : E × F) : F × ℝ :=
  (f z.1 + z.2, r z.2 - delta ^ 2)

noncomputable def jointMap (f : E → F) (r : F → ℝ) (z : (E × F) × ℝ) : F × ℝ :=
  (f z.1.1 + z.1.2, r z.1.2 - z.2 ^ 2)

theorem hasFDerivAt_fixedMap (f : E → F) (r : F → ℝ) (delta : ℝ) (z : E × F)
    (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) (hf : HasFDerivAt f D z.1) (hr : HasFDerivAt r L z.2) :
    HasFDerivAt (fixedMap f r delta) (fixedDerivative D L) z :=
  (AdditiveSubmersion.hasFDerivAt f z D hf).prodMk ((hr.comp z hasFDerivAt_snd).sub_const (delta ^ 2))

theorem hasFDerivAt_jointMap (f : E → F) (r : F → ℝ) (z : (E × F) × ℝ)
    (D : E →L[ℝ] F) (L : F →L[ℝ] ℝ) (hf : HasFDerivAt f D z.1.1) (hr : HasFDerivAt r L z.1.2) :
    HasFDerivAt (jointMap f r) (jointDerivative D L z.2) z := by
  have hh := (AdditiveSubmersion.hasFDerivAt f z.1 D hf).comp z hasFDerivAt_fst
  have hl := ((hr.comp z.1 hasFDerivAt_snd).comp z hasFDerivAt_fst)
  have hd : HasFDerivAt (fun w : (E × F) × ℝ => w.2 ^ 2)
      ((2 * z.2) • ContinuousLinearMap.snd ℝ (E × F) ℝ) z := by
    simpa only [show 2 - 1 = 1 from rfl, pow_one, two_nsmul, two_mul] using
      (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).pow 2
  exact hh.prodMk (hl.sub hd)

theorem jointMap_fderiv_surjective (f : E → F) (r : F → ℝ) (z : (E × F) × ℝ)
    (hf : DifferentiableAt ℝ f z.1.1) (hr : DifferentiableAt ℝ r z.1.2) (hd : z.2 ≠ 0) :
    Function.Surjective (fderiv ℝ (jointMap f r) z) := by
  rw [(hasFDerivAt_jointMap f r z _ _ hf.hasFDerivAt hr.hasFDerivAt).fderiv]
  exact jointDerivative_surjective _ _ _ hd

theorem fixedMap_fderiv_surjective_iff (f : E → F) (r : F → ℝ) (delta : ℝ) (z : E × F)
    (hf : DifferentiableAt ℝ f z.1) (hr : DifferentiableAt ℝ r z.2) :
    Function.Surjective (fderiv ℝ (fixedMap f r delta) z) ↔ (fderiv ℝ r z.2).comp (fderiv ℝ f z.1) ≠ 0 := by
  rw [(hasFDerivAt_fixedMap f r delta z _ _ hf.hasFDerivAt hr.hasFDerivAt).fderiv]
  exact fixedDerivative_surjective_iff _ _

end LeanCanny.Geometry.RadiusLinearization
