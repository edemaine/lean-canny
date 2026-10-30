/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FiniteFiberSlab
public import LeanCanny.Geometry.EndpointMidpoint

/-! # Midpoint signs determine finite slab endpoint incidence

Every arc-to-endpoint edge of the finite slab graph is determined, sufficiently
near that endpoint, by coordinate signs against the other endpoint roots.
One common neighborhood works for all arcs and endpoint labels. Isolated
endpoint roots fail every arc comparison. No regularity at an endpoint is
required. Native stable-interval selection remains a separate obligation.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FiniteFiberSlab
open Set Filter Geometry
open scoped Topology

variable {ι J : Type*} [Finite ι] [Finite J]
variable (H : ℝ → (ι → ℝ) → Prop) {a b : ℝ} (hab : a < b) (curve : J → ℝ → ι → ℝ)
  (hc : ∀ j, ContinuousOn (curve j) (Icc a b))
  (hroot : ∀ j t, t ∈ Icc a b → H t (curve j t))

omit [Finite ι] in
private lemma finite_endpoint (t : ℝ) [Finite (Fiber H t)] : {x | H t x}.Finite := by
  apply (finite_range (fun x : Fiber H t => x.val)).subset
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

include hab hc hroot in
theorem eventually_left_midpoint [Finite (Fiber H a)] :
    ∀ᶠ t in 𝓝[Ioo a b] a, ∀ j, ∀ x : Fiber H a,
      EndpointMidpoint.Matches {y | H a y} x.val (curve j t) ↔
        Edge H curve a b (.inl j) (.inr (.inl x)) := by
  apply eventually_all.mpr
  intro j
  have hlimit : Tendsto (curve j) (𝓝[Ioo a b] a) (𝓝 (curve j a)) :=
    ((hc j a ⟨le_rfl, hab.le⟩).mono Ioo_subset_Icc_self).tendsto
  have h := EndpointMidpoint.eventually_matches_iff (finite_endpoint H a)
    (hroot j a ⟨le_rfl, hab.le⟩) hlimit
  exact h.mono (fun _ ht x => (ht x.val x.property).trans eq_comm)

include hab hc hroot in
theorem eventually_right_midpoint [Finite (Fiber H b)] :
    ∀ᶠ t in 𝓝[Ioo a b] b, ∀ j, ∀ x : Fiber H b,
      EndpointMidpoint.Matches {y | H b y} x.val (curve j t) ↔
        Edge H curve a b (.inl j) (.inr (.inr x)) := by
  apply eventually_all.mpr
  intro j
  have hlimit : Tendsto (curve j) (𝓝[Ioo a b] b) (𝓝 (curve j b)) :=
    ((hc j b ⟨hab.le, le_rfl⟩).mono Ioo_subset_Icc_self).tendsto
  have h := EndpointMidpoint.eventually_matches_iff (finite_endpoint H b)
    (hroot j b ⟨hab.le, le_rfl⟩) hlimit
  exact h.mono (fun _ ht x => (ht x.val x.property).trans eq_comm)

include hab hc hroot in
theorem left_midpoint_iff_of_stable [Finite (Fiber H a)] (j : J) (x : Fiber H a) (s : ℝ)
    (hstable : ∀ t ∈ Ioo a b,
      EndpointMidpoint.Matches {y | H a y} x.val (curve j t) ↔
        EndpointMidpoint.Matches {y | H a y} x.val (curve j s)) :
    EndpointMidpoint.Matches {y | H a y} x.val (curve j s) ↔
      Edge H curve a b (.inl j) (.inr (.inl x)) := by
  have : (𝓝[Ioo a b] a).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hab]
    infer_instance
  obtain ⟨t, ht, hm⟩ := ((eventually_left_midpoint H hab curve hc hroot).and self_mem_nhdsWithin).exists
  exact (hstable t hm).symm.trans (ht j x)

include hab hc hroot in
theorem right_midpoint_iff_of_stable [Finite (Fiber H b)] (j : J) (x : Fiber H b) (s : ℝ)
    (hstable : ∀ t ∈ Ioo a b,
      EndpointMidpoint.Matches {y | H b y} x.val (curve j t) ↔
        EndpointMidpoint.Matches {y | H b y} x.val (curve j s)) :
    EndpointMidpoint.Matches {y | H b y} x.val (curve j s) ↔
      Edge H curve a b (.inl j) (.inr (.inr x)) := by
  have : (𝓝[Ioo a b] b).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    infer_instance
  obtain ⟨t, ht, hm⟩ := ((eventually_right_midpoint H hab curve hc hroot).and self_mem_nhdsWithin).exists
  exact (hstable t hm).symm.trans (ht j x)

include hab hc hroot in
theorem left_midpoint_iff_of_relations [Finite (Fiber H a)] (j : J) (x : Fiber H a) (s : Ioo a b)
    (p : (ι → ℝ) → ι → Polynomial (Polynomial ℝ))
    (hrel : ∀ y, H a y → ∀ i t, t ∈ Ioo a b →
      (p y i).eval₂ (Polynomial.evalRingHom t) (2 * curve j t i - x.val i - y i) = 0)
    (htrail : ∀ y, H a y → ∀ i t, t ∈ Ioo a b → (p y i).trailingCoeff.eval t ≠ 0) :
    EndpointMidpoint.Matches {y | H a y} x.val (curve j s.val) ↔
      Edge H curve a b (.inl j) (.inr (.inl x)) := by
  apply left_midpoint_iff_of_stable H hab curve hc hroot j x s.val
  intro t ht
  exact EndpointMidpoint.matches_iff_of_relations (curve j) (hc j) {y | H a y} x.val p
    hrel htrail ⟨t, ht⟩ s

include hab hc hroot in
theorem right_midpoint_iff_of_relations [Finite (Fiber H b)] (j : J) (x : Fiber H b) (s : Ioo a b)
    (p : (ι → ℝ) → ι → Polynomial (Polynomial ℝ))
    (hrel : ∀ y, H b y → ∀ i t, t ∈ Ioo a b →
      (p y i).eval₂ (Polynomial.evalRingHom t) (2 * curve j t i - x.val i - y i) = 0)
    (htrail : ∀ y, H b y → ∀ i t, t ∈ Ioo a b → (p y i).trailingCoeff.eval t ≠ 0) :
    EndpointMidpoint.Matches {y | H b y} x.val (curve j s.val) ↔
      Edge H curve a b (.inl j) (.inr (.inr x)) := by
  apply right_midpoint_iff_of_stable H hab curve hc hroot j x s.val
  intro t ht
  exact EndpointMidpoint.matches_iff_of_relations (curve j) (hc j) {y | H b y} x.val p
    hrel htrail ⟨t, ht⟩ s

end LeanCanny.Connectivity.FiniteFiberSlab
