/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CircleSublevelLevels
public import LeanCanny.Geometry.CompactSublevelComponents
public import LeanCanny.Geometry.RegularComponentTransport

/-! # A regularity interval preserves connections between zeros

For a nonnegative smooth energy with compact sublevels, positive levels below
the first critical value give the same component relation on its zeros. The
circle lift supplies regular proper fibers and continuous sections; transport
between them combines with compact sublevel limits to recover the exact
zero-set relation at any level in that interval. No regularity of the zeros
or path connectivity of the zero set is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.RegularSublevelComponents
open Set CircleSublevelLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def liftedPoint (x : E) (e : ℝ) : E × ℂ := (x, (Real.sqrt e : ℂ))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem liftedPoint_level (g : E → ℝ) (x : E) (hx : g x = 0) (e : ℝ) (he : 0 ≤ e) :
    energy g (liftedPoint x e) = e := by
  simp only [energy, liftedPoint, hx, zero_add, Complex.normSq_ofReal]
  exact Real.mul_self_sqrt he

theorem component_iff_joined_lift (g : E → ℝ) (hg : ContDiff ℝ 1 g) (e : ℝ) (he : 0 ≤ e)
    (hregular : ∀ z, g z = e → Function.Surjective (fderiv ℝ g z))
    (x y : E) (hx : g x = 0) (hy : g y = 0) :
    y ∈ connectedComponentIn (Base g e) x ↔
      JoinedIn ((energy g) ⁻¹' {e}) (liftedPoint x e) (liftedPoint y e) := by
  have hdiff := hg.differentiable (by norm_num)
  have hcont := contDiff_energy g hg
  let : LocallyPathConnectedSpace (Total g e) := RegularFiber.locallyPathConnected (energy g) e
    (fun _ => hcont.contDiffAt) (fun p => regular_energy g hdiff e hregular p.val p.property)
  let bx : Base g e := ⟨x, by change g x ≤ e; rw [hx]; exact he⟩
  let byy : Base g e := ⟨y, by change g y ≤ e; rw [hy]; exact he⟩
  let sx := sectionMap g e bx
  let sy := sectionMap g e byy
  have hsx : sx.val = liftedPoint x e := by
    change (x, (Real.sqrt (e - g x) : ℂ)) = (x, (Real.sqrt e : ℂ))
    rw [hx, sub_zero]
  have hsy : sy.val = liftedPoint y e := by
    change (y, (Real.sqrt (e - g y) : ℂ)) = (y, (Real.sqrt e : ℂ))
    rw [hy, sub_zero]
  calc
    y ∈ connectedComponentIn (Base g e) x ↔ sy ∈ connectedComponent sx :=
      (section_component_iff g hg.continuous e bx byy).symm
    _ ↔ Joined sx sy := by
      constructor
      · intro h
        exact (connectedComponent_eq_iff_joined sx sy).mp (connectedComponent_eq h)
      · intro h
        rw [(connectedComponent_eq_iff_joined sx sy).mpr h]
        exact mem_connectedComponent
    _ ↔ JoinedIn ((energy g) ⁻¹' {e}) sx.val sy.val := (joinedIn_iff_joined sx.property sy.property).symm
    _ ↔ JoinedIn ((energy g) ⁻¹' {e}) (liftedPoint x e) (liftedPoint y e) := by rw [hsx, hsy]

theorem component_transport (g : E → ℝ) (hg : ContDiff ℝ 1 g) (hnonneg : ∀ x, 0 ≤ g x)
    (hsublevel : ∀ e : ℝ, IsCompact (Base g e)) (δ : ℝ)
    (hregular : ∀ e : ℝ, 0 < e → e ≤ δ → ∀ z, g z = e → Function.Surjective (fderiv ℝ g z))
    (a b : ℝ) (ha : 0 < a) (haδ : a ≤ δ) (hb : 0 < b) (hbδ : b ≤ δ)
    (x y : E) (hx : g x = 0) (hy : g y = 0) :
    y ∈ connectedComponentIn (Base g a) x ↔ y ∈ connectedComponentIn (Base g b) x := by
  let S := Ioc (0 : ℝ) δ
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioc
  have hs (z : E) : Continuous (fun t : S => liftedPoint z t.val) :=
    continuous_const.prodMk (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_subtype_val))
  have hdiff := hg.differentiable (by norm_num)
  have hcont := contDiff_energy g hg
  have hr (p : E × ℂ) (hp : energy g p ∈ S) : Function.Surjective (fderiv ℝ (energy g) p) :=
    regular_energy g hdiff (energy g p) (hregular _ hp.1 hp.2) p rfl
  have h := RegularComponentTransport.joined_sections_iff (energy g) S
    (proper_energy g hg.continuous hnonneg hsublevel) (fun _ _ => hcont.contDiffAt) hr (hs x) (hs y)
    (fun t => liftedPoint_level g x hx t.val t.property.1.le)
    (fun t => liftedPoint_level g y hy t.val t.property.1.le)
    ⟨a, ha, haδ⟩ ⟨b, hb, hbδ⟩
  exact (component_iff_joined_lift g hg a ha.le (hregular a ha haδ) x y hx hy).trans
    (h.trans (component_iff_joined_lift g hg b hb.le (hregular b hb hbδ) x y hx hy).symm)

theorem zero_component_iff_sublevel (g : E → ℝ) (hg : ContDiff ℝ 1 g) (hnonneg : ∀ x, 0 ≤ g x)
    (hsublevel : ∀ e : ℝ, IsCompact (Base g e)) (δ : ℝ) (hδ : 0 < δ)
    (hregular : ∀ e : ℝ, 0 < e → e ≤ δ → ∀ z, g z = e → Function.Surjective (fderiv ℝ g z))
    (x y : E) (hx : g x = 0) (hy : g y = 0) :
    y ∈ connectedComponentIn (g ⁻¹' {0}) x ↔ y ∈ connectedComponentIn (Base g δ) x := by
  have hxK : x ∈ Base g δ := by change g x ≤ δ; rw [hx]; exact hδ.le
  have hz : Base g δ ∩ g ⁻¹' {0} = g ⁻¹' {0} := by
    ext z
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change g z ≤ δ
      rw [show g z = 0 from h]
      exact hδ.le
  have hc := CompactSublevelComponents.mem_zero_component_iff (Base g δ) (hsublevel δ) g hg.continuous
    (fun z _ => hnonneg z) x y hxK hx
  rw [hz] at hc
  constructor
  · intro h
    apply connectedComponentIn_mono x ?_ h
    intro z hz0
    change g z ≤ δ
    rw [show g z = 0 from hz0]
    exact hδ.le
  · intro h
    apply hc.mpr
    intro e he
    have hm := (component_transport g hg hnonneg hsublevel δ hregular δ (min e δ)
      hδ le_rfl (lt_min he hδ) (min_le_right e δ) x y hx hy).mp h
    apply connectedComponentIn_mono x ?_ hm
    intro z hz0
    change g z ≤ min e δ at hz0
    change (g z ≤ δ) ∧ g z ≤ e
    exact ⟨hz0.trans (min_le_right e δ), hz0.trans (min_le_left e δ)⟩

end LeanCanny.Geometry.RegularSublevelComponents
