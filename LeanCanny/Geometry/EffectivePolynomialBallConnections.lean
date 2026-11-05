/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ParameterizedBoundaryCriticalBand
public import LeanCanny.Geometry.ParameterizedBoundaryRadiusBudget
public import LeanCanny.Geometry.PolynomialRadiusWindowTransport
public import LeanCanny.Geometry.BoundedZeroComponents
/-! # Original-bounded balls preserve all polynomial-zero connections

The actual boundary Gram head supplies the compact-band exclusion interval.
Proper two-circle transport and compact residual limits preserve zero-window
components. Exhausting an actual path by its compact norm image then compares
the full, possibly singular and unbounded zero set with one bounded section.
No interval, annihilator, regularity, path model, or stabilization oracle is
an input. The dyadic radius-exponent cutoff has original binary controls.
-/
@[expose] public section
namespace LeanCanny.Geometry.EffectivePolynomialBallConnections
open LeanCanny.Algebra MvPolynomial Set
open PolynomialRadiusSublevelMap PolynomialRadiusWindowPaths
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem zero_component_transport (q : MvPolynomial (Fin n) ℤ) (D H : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H) (a b : ℝ)
    (ha : (2 : ℝ)^ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ a) (hab : a ≤ b)
    (x y : Fin n → ℝ) (hx : q.eval₂ (Int.castRingHom ℝ) x = 0)
    (hy : q.eval₂ (Int.castRingHom ℝ) y = 0) (hxn : normValue x ≤ a) (hyn : normValue y ≤ a) :
    y ∈ connectedComponentIn (Window q 0 a) x ↔ y ∈ connectedComponentIn (Window q 0 b) x := by
  obtain ⟨delta,hdelta,hband⟩ := ParameterizedBoundaryCriticalBand.exists_interval q D H hD hq a b ha
  have HA : 0 < a := (by positivity : (0 : ℝ) < 2^ParameterizedBoundaryRadiusHead.radiusExponent n D H).trans_le ha
  apply PolynomialRadiusWindowTransport.zero_component_transport q D H hD hq a b HA hab delta hdelta
  · intro e he hsmall r hr z lambda hz hn hc
    have HE : (q.eval₂ (Int.castRingHom ℝ) z)^2 = e := by simpa only [residual_eq] using hz
    have HN : (∑ i, z i^2) ∈ Icc a b := by rwa [←normValue_eq_sum,hn]
    exact hband e he hsmall z lambda HE hc HN
  · rw [residual_eq,hx]
    exact zero_pow (by decide)
  · rw [residual_eq,hy]
    exact zero_pow (by decide)
  · exact hxn
  · exact hyn

theorem zero_window (q : MvPolynomial (Fin n) ℤ) (a : ℝ) :
    Window q 0 a = {x | q.eval₂ (Int.castRingHom ℝ) x = 0 ∧ (∑ i, x i^2) ≤ a} := by
  ext x
  constructor
  · rintro ⟨hn,hq⟩
    rw [residual_eq] at hq
    exact ⟨sq_eq_zero_iff.mp (le_antisymm hq (sq_nonneg _)),by simpa only [normValue_eq_sum] using hn⟩
  · rintro ⟨hq,hn⟩
    refine ⟨by simpa only [normValue_eq_sum] using hn,?_⟩
    rw [residual_eq,hq]
    norm_num

theorem joined_iff_section (q : MvPolynomial (Fin n) ℤ) (D H : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H) (a : ℝ)
    (ha : (2 : ℝ)^ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ a)
    (x y : Fin n → ℝ) (hx : q.eval₂ (Int.castRingHom ℝ) x = 0)
    (hy : q.eval₂ (Int.castRingHom ℝ) y = 0) (hxn : (∑ i, x i^2) ≤ a) (hyn : (∑ i, y i^2) ≤ a) :
    JoinedIn {z | q.eval₂ (Int.castRingHom ℝ) z = 0} x y ↔
      JoinedIn {z | q.eval₂ (Int.castRingHom ℝ) z = 0 ∧ (∑ i, z i^2) ≤ a} x y := by
  have HX : x ∈ Window q 0 a := by rw [zero_window]; exact ⟨hx,hxn⟩
  have HY : y ∈ Window q 0 a := by rw [zero_window]; exact ⟨hy,hyn⟩
  constructor
  · rintro ⟨gamma,hgamma⟩
    have HC : IsCompact (normValue '' Set.range gamma) :=
      (isCompact_range gamma.continuous).image
        (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (normPolynomial n)).continuous
    obtain ⟨b,hb⟩ := HC.bddAbove
    have HB : JoinedIn (Window q 0 (max a b)) x y := by
      refine ⟨gamma,fun t => ⟨?_,?_⟩⟩
      · exact (hb ⟨gamma t,Set.mem_range_self t,rfl⟩).trans (le_max_right a b)
      · rw [residual_eq,hgamma t]
        norm_num
    have HXb : x ∈ Window q 0 (max a b) := ⟨HX.1.trans (le_max_left a b),HX.2⟩
    have HYb : y ∈ Window q 0 (max a b) := ⟨HY.1.trans (le_max_left a b),HY.2⟩
    have HCB := (PolynomialRadiusWindowPaths.component_iff_joined q 0 (max a b) x y HXb HYb).mpr HB
    have HCA := (zero_component_transport q D H hD hq a (max a b) ha (le_max_left a b) x y hx hy
      (by simpa only [normValue_eq_sum] using hxn) (by simpa only [normValue_eq_sum] using hyn)).mpr HCB
    have HP := (PolynomialRadiusWindowPaths.component_iff_joined q 0 a x y HX HY).mp HCA
    rwa [zero_window] at HP
  · intro HP
    exact HP.mono (fun _ hz => hz.1)

theorem joined_iff_bounded (q : MvPolynomial (Fin n) ℤ) (D H R : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (hR : (2 : ℝ)^ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ (BoundedZeroSource.radiusSquared R : ℝ))
    (x y : Fin n → ℝ) (hx : x ∈ BoundedZeroSource.Bounded q R) (hy : y ∈ BoundedZeroSource.Bounded q R) :
    JoinedIn (BoundedZeroSource.Original q) x y ↔ JoinedIn (BoundedZeroSource.Bounded q R) x y := by
  simpa only [BoundedZeroSource.Original,BoundedZeroSource.Bounded,BoundedZeroSource.radial] using
    joined_iff_section q D H hD hq (BoundedZeroSource.radiusSquared R : ℝ) hR x y hx.1 hy.1 hx.2 hy.2

theorem joined_iff_after_cutoff (q : MvPolynomial (Fin n) ℤ) (D H R : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (hR : ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ R)
    (x y : Fin n → ℝ) (hx : x ∈ BoundedZeroSource.Bounded q R) (hy : y ∈ BoundedZeroSource.Bounded q R) :
    JoinedIn (BoundedZeroSource.Original q) x y ↔ JoinedIn (BoundedZeroSource.Bounded q R) x y := by
  apply joined_iff_bounded q D H R hD hq ?_ x y hx hy
  simp only [BoundedZeroSource.radiusSquared,Int.cast_pow,Int.cast_ofNat]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem component_iff_after_cutoff (q : MvPolynomial (Fin n) ℤ) (D H R : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^H)
    (hR : ParameterizedBoundaryRadiusHead.radiusExponent n D H ≤ R)
    (x y : Fin n → ℝ) (hx : x ∈ BoundedZeroSource.Bounded q R) (hy : y ∈ BoundedZeroSource.Bounded q R) :
    y ∈ connectedComponentIn (BoundedZeroSource.Original q) x ↔
      y ∈ connectedComponentIn (BoundedZeroSource.Bounded q R) x := by
  constructor
  · intro HC
    have HE : CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ)) = BoundedZeroSource.Original q := by
      ext z
      change (q.map (Int.castRingHom ℝ)).eval z = 0 ↔ q.eval₂ (Int.castRingHom ℝ) z = 0
      rw [MvPolynomial.eval_map]
    have HP : JoinedIn (CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ))) x y := by
      have HX : x ∈ CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ)) := by
        rw [HE]
        exact hx.1
      have HY : y ∈ connectedComponentIn (CoerciveComponentSampling.Zeros (q.map (Int.castRingHom ℝ))) x := by
        rwa [HE]
      exact PolynomialComponentPaths.joinedIn_of_component _ x HX y HY
    rw [HE] at HP
    have HB := (joined_iff_after_cutoff q D H R hD hq hR x y hx hy).mp HP
    rw [connectedComponentIn_eq_image hx]
    exact ⟨⟨y,hy⟩,pathComponent_subset_component _ ((joinedIn_iff_joined hx hy).mp HB),rfl⟩
  · intro HC
    exact connectedComponentIn_mono x
      (show BoundedZeroSource.Bounded q R ⊆ BoundedZeroSource.Original q from fun _ hz => hz.1) HC

end LeanCanny.Geometry.EffectivePolynomialBallConnections
