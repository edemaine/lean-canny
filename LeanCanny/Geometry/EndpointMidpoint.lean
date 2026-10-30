/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Constructions
public import Mathlib.Order.Filter.Finite
public import LeanCanny.Geometry.AlgebraicBranchSign

/-! # Identifying finite endpoint limits by midpoint signs

A convergent branch eventually identifies its endpoint among finitely many
candidates by coordinate comparisons with pairwise midpoints. The candidate
need not have a coordinate distinct from every other candidate in the same
position. No separation radius or digits of a nearby rational point are used.
-/

@[expose] public section
namespace LeanCanny.Geometry.EndpointMidpoint
open Filter Set
open scoped Topology

variable {ι α : Type*}

def Side (x y u : ι → ℝ) : Prop :=
  ∀ i, (x i < y i → u i < (x i + y i) / 2) ∧
    (y i < x i → (x i + y i) / 2 < u i)

def Matches (S : Set (ι → ℝ)) (x u : ι → ℝ) : Prop := ∀ y ∈ S, Side x y u

lemma eventually_side [Finite ι] {L : Filter α} {f : α → ι → ℝ} {x : ι → ℝ}
    (hf : Tendsto f L (𝓝 x)) (y : ι → ℝ) : ∀ᶠ t in L, Side x y (f t) := by
  apply eventually_all.mpr
  intro i
  have hi : Tendsto (fun t => f t i) L (𝓝 (x i)) := (continuous_apply i).tendsto x |>.comp hf
  have hleft : ∀ᶠ t in L, x i < y i → f t i < (x i + y i) / 2 := by
    by_cases hxy : x i < y i
    · exact (hi.eventually (Iio_mem_nhds (by linarith : x i < (x i + y i) / 2))).mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (hxy ht).elim)
  have hright : ∀ᶠ t in L, y i < x i → (x i + y i) / 2 < f t i := by
    by_cases hyx : y i < x i
    · exact (hi.eventually (Ioi_mem_nhds (by linarith : (x i + y i) / 2 < x i))).mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (hyx ht).elim)
  exact hleft.and hright

lemma eventually_not_side {L : Filter α} {f : α → ι → ℝ} {z x : ι → ℝ}
    (hf : Tendsto f L (𝓝 z)) (hx : x ≠ z) : ∀ᶠ t in L, ¬Side x z (f t) := by
  classical
  have hex : ∃ i, x i ≠ z i := by
    by_contra h
    exact hx (funext (fun i => by simpa using not_exists.mp h i))
  obtain ⟨i, hi⟩ := hex
  have hc : Tendsto (fun t => f t i) L (𝓝 (z i)) := (continuous_apply i).tendsto z |>.comp hf
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hm : (x i + z i) / 2 < z i := by linarith
    exact (hc.eventually (Ioi_mem_nhds hm)).mono (fun _ ht hs => (not_lt_of_gt ht) ((hs i).1 hlt))
  · have hm : z i < (x i + z i) / 2 := by linarith
    exact (hc.eventually (Iio_mem_nhds hm)).mono (fun _ ht hs => (not_lt_of_gt ht) ((hs i).2 hgt))

/-- One common neighborhood works for every endpoint candidate and every
midpoint comparison. This also covers a zero-dimensional endpoint fiber. -/
theorem eventually_matches_iff [Finite ι] {L : Filter α} {f : α → ι → ℝ}
    {z : ι → ℝ} {S : Set (ι → ℝ)} (hS : S.Finite) (hz : z ∈ S)
    (hf : Tendsto f L (𝓝 z)) :
    ∀ᶠ t in L, ∀ x ∈ S, Matches S x (f t) ↔ x = z := by
  classical
  apply hS.eventually_all.mpr
  intro x _
  by_cases hx : x = z
  · subst x
    have h := hS.eventually_all.mpr (fun y _ => eventually_side hf y)
    exact h.mono (fun _ ht => ⟨fun _ => rfl, fun _ => ht⟩)
  · exact (eventually_not_side hf hx).mono (fun _ ht =>
      ⟨fun hm => (ht (hm z hz)).elim, fun he => (hx he).elim⟩)

/-- An eventual midpoint label denotes exactly the actual endpoint. -/
theorem matches_limit_iff [Finite ι] {L : Filter α} [L.NeBot] {f : α → ι → ℝ}
    {z x : ι → ℝ} {S : Set (ι → ℝ)} (hS : S.Finite) (hz : z ∈ S) (hx : x ∈ S)
    (hf : Tendsto f L (𝓝 z)) : (∀ᶠ t in L, Matches S x (f t)) ↔ x = z := by
  constructor
  · intro hm
    have h := (eventually_matches_iff hS hz hf).and hm
    obtain ⟨t, ht, hm⟩ := h.exists
    exact (ht x hx).mp hm
  · intro he
    exact (eventually_matches_iff hS hz hf).mono (fun _ ht => (ht x hx).mpr he)

/-- Polynomial-value relations with nonvanishing trailing coefficients make
all midpoint comparisons constant on a retained open interval. Tests that
vanish identically are allowed and yield neither strict side. -/
theorem matches_iff_of_relations {a b : ℝ} (curve : ℝ → ι → ℝ)
    (hc : ContinuousOn curve (Icc a b)) (S : Set (ι → ℝ)) (x : ι → ℝ)
    (p : (ι → ℝ) → ι → Polynomial (Polynomial ℝ))
    (hrel : ∀ y ∈ S, ∀ i t, t ∈ Ioo a b →
      (p y i).eval₂ (Polynomial.evalRingHom t) (2 * curve t i - x i - y i) = 0)
    (htrail : ∀ y ∈ S, ∀ i t, t ∈ Ioo a b → (p y i).trailingCoeff.eval t ≠ 0)
    (s t : Ioo a b) : Matches S x (curve s.val) ↔ Matches S x (curve t.val) := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hcurve : Continuous (fun u : Ioo a b => curve u.val) :=
    continuousOn_iff_continuous_domRestrict.mp (hc.mono Ioo_subset_Icc_self)
  have hside (y : ι → ℝ) (hy : y ∈ S) : Side x y (curve s.val) ↔ Side x y (curve t.val) := by
    have hs (i : ι) := AlgebraicBranchSign.sign_iff (p y i) Subtype.val
      (fun u : Ioo a b => 2 * curve u.val i - x i - y i) continuous_subtype_val
      (((continuous_apply i).comp hcurve).const_mul 2 |>.sub continuous_const |>.sub continuous_const)
      (fun u => hrel y hy i u.val u.property) (fun u => htrail y hy i u.val u.property) s t
    have himp (u v : ι → ℝ)
        (h : ∀ i, (2 * u i - x i - y i < 0 ↔ 2 * v i - x i - y i < 0) ∧
          (0 < 2 * u i - x i - y i ↔ 0 < 2 * v i - x i - y i)) : Side x y u → Side x y v := by
      intro hu i
      constructor
      · intro hxy
        have hh := (hu i).1 hxy
        have ht := (h i).1.mp (by linarith : 2 * u i - x i - y i < 0)
        linarith
      · intro hyx
        have hh := (hu i).2 hyx
        have ht := (h i).2.mp (by linarith : 0 < 2 * u i - x i - y i)
        linarith
    exact ⟨himp _ _ hs, himp _ _ (fun i => ⟨(hs i).1.symm, (hs i).2.symm⟩)⟩
  exact ⟨fun h y hy => (hside y hy).mp (h y hy), fun h y hy => (hside y hy).mpr (h y hy)⟩

end LeanCanny.Geometry.EndpointMidpoint
