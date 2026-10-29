/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UnivariateRootFamily
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-! # Proper projections of coordinate polynomial families

Nonvanishing leading coefficients give compact bounds on roots over every
compact parameter set. Hence projection is proper on any retained parameter
set where the leading coefficients stay nonzero. Repeated roots need no
regularity assumption. Monic coordinate families are proper globally.
-/

@[expose] public section
namespace LeanCanny.Geometry.PolynomialCoordinateProper
open Set Polynomial Topology
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def bound (Q : Polynomial (Polynomial ℝ)) (t : ℝ) : NNReal :=
  (Finset.range Q.natDegree).sup (fun i => ‖(Q.coeff i).eval t‖₊) / ‖Q.leadingCoeff.eval t‖₊ + 1

lemma continuous_bound (Q : Polynomial (Polynomial ℝ)) (s : Set ℝ)
    (hl : ∀ t ∈ s, Q.leadingCoeff.eval t ≠ 0) : ContinuousOn (bound Q) s := by
  have hn : Continuous (fun t => (Finset.range Q.natDegree).sup (fun i => ‖(Q.coeff i).eval t‖₊)) :=
    Continuous.finset_sup_apply (fun i _ => (Q.coeff i).continuous.nnnorm)
  have hd : Continuous (fun t => ‖Q.leadingCoeff.eval t‖₊) := Q.leadingCoeff.continuous.nnnorm
  exact (hn.continuousOn.div₀ hd.continuousOn (fun t ht => by
    intro hz
    apply hl t ht
    apply norm_eq_zero.mp
    have H := congrArg (fun v : NNReal => (v : ℝ)) hz
    simpa only [coe_nnnorm, NNReal.coe_zero] using H)).add continuousOn_const

lemma bound_eq (Q : Polynomial (Polynomial ℝ)) (t : ℝ) (hl : Q.leadingCoeff.eval t ≠ 0) :
    bound Q t = (Q.map (Polynomial.evalRingHom t)).cauchyBound := by
  have hdeg : (Q.map (Polynomial.evalRingHom t)).natDegree = Q.natDegree :=
    Polynomial.natDegree_map_eq_iff.mpr (Or.inl hl)
  unfold bound Polynomial.cauchyBound
  rw [hdeg, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hl]
  simp only [Polynomial.coeff_map, Polynomial.coe_evalRingHom]

lemma root_bound (Q : Polynomial (Polynomial ℝ)) (t x : ℝ) (hl : Q.leadingCoeff.eval t ≠ 0)
    (hx : Q.eval₂ (Polynomial.evalRingHom t) x = 0) : ‖x‖₊ < bound Q t := by
  rw [bound_eq Q t hl]
  have hp : Q.map (Polynomial.evalRingHom t) ≠ 0 := by
    intro hz
    have H := congrArg Polynomial.leadingCoeff hz
    rw [Polynomial.leadingCoeff_zero, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hl] at H
    exact hl H
  apply Polynomial.IsRoot.norm_lt_cauchyBound hp
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hx

lemma bounded_roots_on_compact (Q : Polynomial (Polynomial ℝ)) (K : Set ℝ) (hK : IsCompact K)
    (hl : ∀ t ∈ K, Q.leadingCoeff.eval t ≠ 0) :
    ∃ B : NNReal, ∀ t ∈ K, ∀ x : ℝ, Q.eval₂ (Polynomial.evalRingHom t) x = 0 → ‖x‖₊ ≤ B := by
  obtain ⟨B, hB⟩ := (hK.image_of_continuousOn (continuous_bound Q K hl)).bddAbove
  refine ⟨B, ?_⟩
  intro t ht x hx
  exact (root_bound Q t x (hl t ht) hx).le.trans (hB (Set.mem_image_of_mem _ ht))

open LeanCanny.Geometry
lemma proper_restriction {ι : Type*} [Fintype ι]
    (Q : ι → Polynomial (Polynomial ℝ)) (s : Set ℝ)
    (hl : ∀ i t, t ∈ s → (Q i).leadingCoeff.eval t ≠ 0) :
    IsProperMap (s.restrictPreimage (RootProjection.projection
      (PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q)))) := by
  let f := PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q)
  change IsProperMap (s.restrictPreimage (RootProjection.projection f))
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨(RootProjection.continuous_projection f).restrictPreimage, ?_⟩
  intro K hK
  let C : Set ℝ := Subtype.val '' K
  have hC : IsCompact C := hK.image continuous_subtype_val
  have hb (i : ι) : ∃ B : NNReal, ∀ t ∈ C, ∀ x : ℝ,
      (Q i).eval₂ (Polynomial.evalRingHom t) x = 0 → ‖x‖₊ ≤ B := by
    apply bounded_roots_on_compact (Q i) C hC
    rintro t ⟨u, _, rfl⟩
    exact hl i u.val u.property
  choose B hB using hb
  let U : Set (ι → ℝ) := {x | ∀ i, x i ∈ Metric.closedBall (0 : ℝ) (B i : ℝ)}
  have hU : IsCompact U := isCompact_pi_infinite (fun i => isCompact_closedBall 0 (B i : ℝ))
  have hbound (t : ℝ) (ht : t ∈ C) (x : ι → ℝ) (hx : f (t, x) = 0) : x ∈ U := by
    intro i
    have H : (Q i).eval₂ (Polynomial.evalRingHom t) (x i) = 0 := by
      have H := congrFun hx i
      change PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q) (t, x) i = 0 at H
      simpa only [UnivariateRootFamily.value_diagonal] using H
    have Hbound := hB i t ht (x i) H
    rw [Metric.mem_closedBall, dist_zero_right]
    exact_mod_cast Hbound
  let A : Set (ℝ × (ι → ℝ)) := {z | f z = 0 ∧ z.1 ∈ C}
  have hAclosed : IsClosed A :=
    (isClosed_eq (PolynomialRootFamily.contDiff_value _ 1).continuous continuous_const).inter
      (hC.isClosed.preimage continuous_fst)
  have hA : IsCompact A := (hC.prod hU).of_isClosed_subset hAclosed
    (fun z hz => ⟨hz.2, hbound z.1 hz.2 z.2 hz.1⟩)
  let read : (RootProjection.projection f ⁻¹' s) → ℝ × (ι → ℝ) := fun z => z.val.val
  have hemb : IsEmbedding read := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  rw [hemb.isCompact_iff]
  have he : read '' ((s.restrictPreimage (RootProjection.projection f)) ⁻¹' K) = A := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.val.property, ⟨s.restrictPreimage (RootProjection.projection f) w, hw, rfl⟩⟩
    · rintro ⟨hz, ht⟩
      obtain ⟨u, hu, hparam⟩ := ht
      let w : (RootProjection.projection f ⁻¹' s) := ⟨⟨z, hz⟩, by
        change z.1 ∈ s
        rw [← hparam]
        exact u.property⟩
      have hw : s.restrictPreimage (RootProjection.projection f) w = u := Subtype.ext hparam.symm
      have hmem : w ∈ (s.restrictPreimage (RootProjection.projection f)) ⁻¹' K := by
        change s.restrictPreimage (RootProjection.projection f) w ∈ K
        rw [hw]
        exact hu
      exact ⟨w, hmem, rfl⟩
  rw [he]
  exact hA

lemma proper {ι : Type*} [Fintype ι] (Q : ι → Polynomial (Polynomial ℝ))
    (hl : ∀ i t, (Q i).leadingCoeff.eval t ≠ 0) :
    IsProperMap (RootProjection.projection (PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q))) := by
  let f := PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q)
  have hp : IsProperMap ((Set.univ : Set ℝ).restrictPreimage (RootProjection.projection f)) :=
    proper_restriction Q Set.univ (fun i t _ => hl i t)
  have hc : IsProperMap ((RootProjection.projection f) ∘
      (Subtype.val : (RootProjection.projection f ⁻¹' (Set.univ : Set ℝ)) → RootProjection.Space f)) :=
    (Homeomorph.Set.univ ℝ).isProperMap.comp hp
  exact isProperMap_of_comp_of_surj continuous_subtype_val (RootProjection.continuous_projection f) hc
    (fun z => ⟨⟨z, Set.mem_univ _⟩, rfl⟩)

lemma proper_of_monic {ι : Type*} [Fintype ι] (Q : ι → Polynomial (Polynomial ℝ))
    (hQ : ∀ i, (Q i).Monic) :
    IsProperMap (RootProjection.projection (PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q))) := by
  apply proper Q
  intro i t
  rw [(hQ i).leadingCoeff]
  simp
end LeanCanny.Geometry.PolynomialCoordinateProper
