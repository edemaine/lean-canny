/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CircleSublevelLift
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Order.Filter.AtTopBot.Ring

/-! # Connected pure-power slack fibers

For odd m, the coordinate power t ↦ t^m is a real homeomorphism. It identifies
g(x) + u^(2m) + v^(2m) = e with the circle lift. Thus adding two slack variables
of the same pure-power degree preserves the sublevel's components, without
introducing quadratic leading terms in those variables.
-/

@[expose] public section
namespace LeanCanny.Geometry.PurePowerSublevelLift
open Set Filter

theorem real_pow_surjective (m : ℕ) (hm : Odd m) : Function.Surjective (fun x : ℝ => x ^ m) := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have ht : Tendsto (fun x : ℝ => x ^ m) atTop atTop := tendsto_pow_atTop hm0
  have hb : Tendsto (fun x : ℝ => -((-x) ^ m)) atBot atBot :=
    tendsto_neg_atTop_atBot.comp (ht.comp tendsto_neg_atBot_atTop)
  apply (continuous_id.pow m).surjective ht
  change Tendsto (fun x : ℝ => x ^ m) atBot atBot
  simpa only [hm.neg_pow, neg_neg] using hb

noncomputable def realPower (m : ℕ) (hm : Odd m) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (fun x : ℝ => x ^ m) hm.strictMono_pow (real_pow_surjective m hm)).toHomeomorph

theorem realPower_apply (m : ℕ) (hm : Odd m) (x : ℝ) : realPower m hm x = x ^ m := rfl

noncomputable def powerMap (m : ℕ) (hm : Odd m) : ℂ ≃ₜ ℂ :=
  (Complex.equivRealProdCLM.toHomeomorph.trans ((realPower m hm).prodCongr (realPower m hm))).trans
    Complex.equivRealProdCLM.toHomeomorph.symm

theorem powerMap_re (m : ℕ) (hm : Odd m) (z : ℂ) : (powerMap m hm z).re = z.re ^ m := rfl
theorem powerMap_im (m : ℕ) (hm : Odd m) (z : ℂ) : (powerMap m hm z).im = z.im ^ m := rfl

def penalty (m : ℕ) (z : ℂ) : ℝ := z.re ^ (2 * m) + z.im ^ (2 * m)

theorem normSq_powerMap (m : ℕ) (hm : Odd m) (z : ℂ) :
    Complex.normSq (powerMap m hm z) = penalty m z := by
  simp only [Complex.normSq_apply, powerMap_re, powerMap_im, penalty, ← pow_two, ← pow_mul, Nat.mul_comm m 2]

def Total {X : Type*} (m : ℕ) (g : X → ℝ) (e : ℝ) := {p : X × ℂ | g p.1 + penalty m p.2 = e}

section Topology
variable {X : Type*} [TopologicalSpace X]

noncomputable def spaceMap (m : ℕ) (hm : Odd m) : X × ℂ ≃ₜ X × ℂ :=
  (Homeomorph.refl X).prodCongr (powerMap m hm)

theorem total_eq_preimage (m : ℕ) (hm : Odd m) (g : X → ℝ) (e : ℝ) :
    Total m g e = (spaceMap m hm) ⁻¹' CircleSublevelLift.Total g e := by
  ext p
  change (g p.1 + penalty m p.2 = e) ↔ g p.1 + Complex.normSq (powerMap m hm p.2) = e
  rw [normSq_powerMap]

noncomputable def levelHomeomorph (m : ℕ) (hm : Odd m) (g : X → ℝ) (e : ℝ) :
    Total m g e ≃ₜ CircleSublevelLift.Total g e :=
  (spaceMap m hm).sets (total_eq_preimage m hm g e)

noncomputable def projection (m : ℕ) (hm : Odd m) (g : X → ℝ) (e : ℝ)
    (p : Total m g e) : CircleSublevelLift.Base g e :=
  CircleSublevelLift.projection g e (levelHomeomorph m hm g e p)

noncomputable def sectionMap (m : ℕ) (hm : Odd m) (g : X → ℝ) (e : ℝ)
    (x : CircleSublevelLift.Base g e) : Total m g e :=
  (levelHomeomorph m hm g e).symm (CircleSublevelLift.sectionMap g e x)

theorem projection_section (m : ℕ) (hm : Odd m) (g : X → ℝ) (e : ℝ)
    (x : CircleSublevelLift.Base g e) : projection m hm g e (sectionMap m hm g e x) = x := by
  simp only [projection, sectionMap, Homeomorph.apply_symm_apply, CircleSublevelLift.projection_section]

theorem quotient_projection (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ) :
    Topology.IsQuotientMap (projection m hm g e) :=
  (CircleSublevelLift.quotient_projection g hg e).comp (levelHomeomorph m hm g e).isQuotientMap

theorem fiber_connected (m : ℕ) (hm : Odd m) (g : X → ℝ) (e : ℝ) (x : CircleSublevelLift.Base g e) :
    IsConnected ((projection m hm g e) ⁻¹' {x}) := by
  have he : (projection m hm g e) ⁻¹' {x} =
      (levelHomeomorph m hm g e).symm '' ((CircleSublevelLift.projection g e) ⁻¹' {x}) := by
    ext p
    constructor
    · intro hp
      exact ⟨levelHomeomorph m hm g e p, hp, (levelHomeomorph m hm g e).symm_apply_apply p⟩
    · rintro ⟨q, hq, rfl⟩
      change CircleSublevelLift.projection g e
        (levelHomeomorph m hm g e ((levelHomeomorph m hm g e).symm q)) = x
      rw [Homeomorph.apply_symm_apply]
      exact hq
  rw [he]
  exact (CircleSublevelLift.fiber_connected g e x).image _ (levelHomeomorph m hm g e).symm.continuous.continuousOn

theorem component_preimage (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ) (p : Total m g e) :
    (projection m hm g e) ⁻¹' connectedComponent (projection m hm g e p) = connectedComponent p :=
  (quotient_projection m hm g hg e).isCoinducing.preimage_connectedComponent (fiber_connected m hm g e) p

theorem section_component_iff (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ)
    (x y : CircleSublevelLift.Base g e) :
    sectionMap m hm g e y ∈ connectedComponent (sectionMap m hm g e x) ↔
      y.val ∈ connectedComponentIn (CircleSublevelLift.Base g e) x.val := by
  rw [← component_preimage m hm g hg e, mem_preimage, projection_section, projection_section,
    connectedComponentIn_eq_image x.property]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨z, hz, he⟩
    exact (Subtype.ext he : z = y) ▸ hz

theorem preconnected_iff (m : ℕ) (hm : Odd m) (g : X → ℝ) (hg : Continuous g) (e : ℝ) :
    IsPreconnected (Total m g e) ↔ IsPreconnected (CircleSublevelLift.Base g e) := by
  rw [total_eq_preimage m hm g e, (spaceMap m hm).isPreconnected_preimage]
  exact CircleSublevelLift.preconnected_iff g hg e

end Topology
end LeanCanny.Geometry.PurePowerSublevelLift
