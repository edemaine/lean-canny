/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.PolynomialRadiusWindowPaths
public import LeanCanny.Geometry.TwoCircleSublevelSections
public import LeanCanny.Geometry.RegularComponentTransport
public import LeanCanny.Geometry.CompactSublevelComponents
/-! # Radius transport and compact residual limits in the original tuple -/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialRadiusWindowTransport
open LeanCanny.Algebra MvPolynomial Set PolynomialRadiusSublevelMap PolynomialRadiusWindowPaths
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def lifted (q : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) (t : ℝ × ℝ) :=
  TwoCircleSublevelSections.point (residual q) normValue t.1 t.2 x

theorem continuous_lifted (q : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) : Continuous (lifted q x) :=
  continuous_const.prodMk
    ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_fst.sub continuous_const))).prodMk
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_snd.sub continuous_const))))

theorem component_iff_lift (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (x y : Fin n → ℝ)
    (hx : x ∈ Window q e r) (hy : y ∈ Window q e r) :
    y ∈ connectedComponentIn (Window q e r) x ↔
      JoinedIn ((map q) ⁻¹' {(e,r)}) (lifted q x (e,r)) (lifted q y (e,r)) :=
  (component_iff_joined q e r x y hx hy).trans
    (TwoCircleSublevelSections.joined_iff (residual q) normValue
      (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (q^2)).continuous
      (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (normPolynomial n)).continuous e r x y)

theorem component_transport (q : MvPolynomial (Fin n) ℤ) (e a b : ℝ)
    (he : 0 < e) (ha : 0 < a) (hab : a ≤ b)
    (hregular : ∀ x : Fin n → ℝ, residual q x = e → Function.Surjective (fderiv ℝ (residual q) x))
    (hboundary : ∀ r ∈ Icc a b, ∀ (x : Fin n → ℝ) (lambda : ℝ), residual q x = e → normValue x = r →
      ¬ ∀ i, 2*x i + lambda*(2*q.eval₂ (Int.castRingHom ℝ) x*(pderiv i q).eval₂ (Int.castRingHom ℝ) x)=0)
    (x y : Fin n → ℝ) (hx : residual q x = 0) (hy : residual q y = 0)
    (hxn : normValue x ≤ a) (hyn : normValue y ≤ a) :
    y ∈ connectedComponentIn (Window q e a) x ↔ y ∈ connectedComponentIn (Window q e b) x := by
  let S : Set (ℝ × ℝ) := {e} ×ˢ Icc a b
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_singleton.prod isPreconnected_Icc)
  let sx : S → (Fin n → ℝ) × (ℂ × ℂ) := fun t => lifted q x t.val
  let sy : S → (Fin n → ℝ) × (ℂ × ℂ) := fun t => lifted q y t.val
  have HS (v : Fin n → ℝ) (hv : residual q v = 0) (hvn : normValue v ≤ a) (t : S) :
      map q (lifted q v t.val) = t.val := by
    apply TwoCircleSublevelSections.point_level
    refine ⟨hvn.trans t.property.2.1,?_⟩
    rw [hv,show t.val.1=e from t.property.1]
    exact he.le
  have HR (p : (Fin n → ℝ) × (ℂ × ℂ)) (hp : map q p ∈ S) :
      Function.Surjective (fderiv ℝ (map q) p) := by
    apply PolynomialRadiusSublevelMap.regular q e (map q p).2 (ha.trans_le hp.2.1) hregular
      (hboundary _ hp.2) p
    exact Prod.ext hp.1 rfl
  let ta : S := ⟨(e,a),rfl,le_rfl,hab⟩
  let tb : S := ⟨(e,b),rfl,hab,le_rfl⟩
  have H := RegularComponentTransport.joined_sections_iff (map q) S (proper q)
    (fun _ _ => (smooth q).contDiffAt) HR
    ((continuous_lifted q x).comp continuous_subtype_val)
    ((continuous_lifted q y).comp continuous_subtype_val)
    (HS x hx hxn) (HS y hy hyn) ta tb
  have Hxa : x ∈ Window q e a := ⟨hxn,by rw [hx]; exact he.le⟩
  have Hya : y ∈ Window q e a := ⟨hyn,by rw [hy]; exact he.le⟩
  have Hxb : x ∈ Window q e b := ⟨hxn.trans hab,by rw [hx]; exact he.le⟩
  have Hyb : y ∈ Window q e b := ⟨hyn.trans hab,by rw [hy]; exact he.le⟩
  exact (component_iff_lift q e a x y Hxa Hya).trans
    (H.trans (component_iff_lift q e b x y Hxb Hyb).symm)

theorem zero_component_iff (q : MvPolynomial (Fin n) ℤ) (r : ℝ) (hr : 0 ≤ r)
    (x y : Fin n → ℝ) (hxn : normValue x ≤ r) (hx : residual q x = 0) :
    y ∈ connectedComponentIn (Window q 0 r) x ↔
      ∀ e : ℝ, 0 < e → y ∈ connectedComponentIn (Window q e r) x := by
  let K : Set (Fin n → ℝ) := {x | normValue x ≤ r}
  have HK : IsCompact K := by
    simpa only [K,normValue_eq_distance] using SquaredDistanceFibers.compact_sublevel (0 : Fin n → ℝ) r hr
  have H := CompactSublevelComponents.sublevel_component K HK (residual q)
    (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (q^2)).continuous x ⟨hxn,hx.le⟩
  change y ∈ connectedComponentIn (CompactSublevelComponents.sublevel K (residual q) 0) x ↔ _
  rw [H]
  simp only [mem_iInter,Subtype.forall,mem_Ioi]
  rfl

theorem zero_component_transport (q : MvPolynomial (Fin n) ℤ) (D H : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (delta : ℝ) (hdelta : 0 < delta)
    (hboundary : ∀ e : ℝ, 0 < e → e < delta → ∀ r ∈ Icc a b,
      ∀ (x : Fin n → ℝ) (lambda : ℝ), residual q x = e → normValue x = r →
        ¬ ∀ i, 2*x i + lambda*(2*q.eval₂ (Int.castRingHom ℝ) x*(pderiv i q).eval₂ (Int.castRingHom ℝ) x)=0)
    (x y : Fin n → ℝ) (hx : residual q x = 0) (hy : residual q y = 0)
    (hxn : normValue x ≤ a) (hyn : normValue y ≤ a) :
    y ∈ connectedComponentIn (Window q 0 a) x ↔ y ∈ connectedComponentIn (Window q 0 b) x := by
  constructor
  · apply connectedComponentIn_mono x
    intro z hz
    exact ⟨hz.1.trans hab,hz.2⟩
  · intro HB
    apply (zero_component_iff q a ha.le x y hxn hx).mpr
    intro e he
    let safe := GeneralCriticalValueBounds.level n (2*D+1) (2*H)
    have HS : 0 < safe := GeneralCriticalValueBounds.level_pos _ _ _
    let eta := min e (min delta safe) / 2
    have HP : 0 < eta := half_pos (lt_min he (lt_min hdelta HS))
    have HE : eta ≤ e := (half_le_self (lt_min he (lt_min hdelta HS)).le).trans (min_le_left _ _)
    have HT : eta < min delta safe :=
      (half_lt_self (lt_min he (lt_min hdelta HS))).trans_le (min_le_right _ _)
    have HD : eta < delta := HT.trans_le (min_le_left _ _)
    have HV : eta ≤ safe := HT.le.trans (min_le_right _ _)
    have HBa : y ∈ connectedComponentIn (Window q eta b) x := by
      apply connectedComponentIn_mono x ?_ HB
      intro z hz
      exact ⟨hz.1,hz.2.trans HP.le⟩
    have HA := (component_transport q eta a b HP ha hab
      (small_regular q D H hD hq eta HP HV) (hboundary eta HP HD) x y hx hy hxn hyn).mpr HBa
    apply connectedComponentIn_mono x ?_ HA
    intro z hz
    exact ⟨hz.1,hz.2.trans HE⟩

end LeanCanny.Geometry.PolynomialRadiusWindowTransport
