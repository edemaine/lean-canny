/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ParameterizedCriticalBranches
public import LeanCanny.Geometry.CoordinateSlice
public import LeanCanny.Geometry.PolynomialHypersurfaceSweep
public import LeanCanny.Connectivity.RegularRootArcs

/-! # Complete critical arcs for coordinate sweeps on fixed hypersurfaces

The polynomial parameter is the swept coordinate. Compactness of the original
level bounds all spatial critical roots, including exceptional endpoint roots.
One integer direction works throughout the sweep. Outside a constructed finite
exceptional set, its spatial roots form complete anchored arcs, continuous at
both ends. The reciprocal variable is absent from this proper root family.

This construction does not yet bound the effective encodings of the arcs.
-/

@[expose] public section

namespace LeanCanny.Connectivity.CoordinateCriticalArcs
open Set MvPolynomial Geometry
open LeanCanny.Algebra
open ProjectionFiniteSpecialization

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable abbrev equation (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ) :=
  CoordinateSlice.family base (p - C c)

noncomputable abbrev system (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base) (u : DirectionIndex pivot → ℕ) :=
  ParameterizedCriticalBranches.system (equation p base c) pivot u

omit [Fintype ι] in
theorem eval_equation (p : MvPolynomial ι ℝ) (base : ι) (c t : ℝ)
    (x : CoordinateSlice.Index base → ℝ) :
    (equation p base c).eval₂ (Polynomial.evalRingHom t) x =
      p.eval (CoordinateSlice.restore base t x) - c := by
  have he := CoordinateSlice.eval_family base (p - C c) (RingHom.id ℝ) t x
  simpa only [Polynomial.evalRingHom, eval₂_sub, eval₂_C, RingHom.id_apply,
    eval₂_id] using he

omit [Fintype ι] in
theorem root_level (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base) (u : DirectionIndex pivot → ℕ)
    (t : ℝ) (x : CoordinateSlice.Index base → ℝ)
    (hx : system p base c pivot u (t, x) = 0) :
    p.eval (CoordinateSlice.restore base t x) = c := by
  have hq := ((ParameterizedCriticalBranches.system_iff _ pivot u t x).mp hx).1
  rwa [eval_equation, sub_eq_zero] at hq

theorem isProperMap (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base) (u : DirectionIndex pivot → ℕ)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    IsProperMap (RootProjection.projection (system p base c pivot u)) := by
  let K := (fun x : ι → ℝ => fun j : CoordinateSlice.Index base => x j.val) ''
    {x : ι → ℝ | p.eval x = c}
  have hK : IsCompact K := (hp.isCompact_preimage isCompact_singleton).image
    (continuous_pi fun j => continuous_apply j.val)
  apply PolynomialRootFamily.isProperMap_of_compact_bound _ hK
  intro t x hx
  refine ⟨CoordinateSlice.restore base t x, root_level p base c pivot u t x hx, ?_⟩
  funext j
  exact CoordinateSlice.restore_other base t x j

theorem slice_regular (p : MvPolynomial ι ℝ) (base : ι) (c t : ℝ)
    (x : CoordinateSlice.Index base → ℝ)
    (hregular : Function.Surjective (fderiv ℝ
      (HypersurfaceSweep.combined (fun y => p.eval y) (fun y => y base))
        (CoordinateSlice.restore base t x))) :
    Function.Surjective (fderiv ℝ
      (fun y => (equation p base c).eval₂ (Polynomial.evalRingHom t) y) x) := by
  have he : (fun y : CoordinateSlice.Index base → ℝ =>
      (equation p base c).eval₂ (Polynomial.evalRingHom t) y) =
      (fun y => (CoordinateSlice.family base p).eval₂ (Polynomial.evalRingHom t) y - c) := by
    funext y
    rw [eval_equation]
    have h := CoordinateSlice.eval_family base p (RingHom.id ℝ) t y
    simpa only [Polynomial.evalRingHom, eval₂_id] using congrArg (fun z : ℝ => z - c) h.symm
  rw [he, fderiv_sub_const]
  have h := CoordinateSlice.surjective_fderiv_family base p (RingHom.id ℝ) t x
    (by simpa only [eval₂_id] using hregular)
  simpa only [Polynomial.evalRingHom] using h

omit [Fintype ι] in
theorem isCompact_slice (p : MvPolynomial ι ℝ) (base : ι) (c t : ℝ)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    IsCompact {x : CoordinateSlice.Index base → ℝ |
      (equation p base c).eval₂ (Polynomial.evalRingHom t) x = 0} := by
  have hK := (CoordinateSlice.isProperMap_restore base t).isCompact_preimage
    (hp.isCompact_preimage (K := {c}) isCompact_singleton)
  have he : {x : CoordinateSlice.Index base → ℝ |
      (equation p base c).eval₂ (Polynomial.evalRingHom t) x = 0} =
      CoordinateSlice.restore base t ⁻¹' ((fun x => p.eval x) ⁻¹' {c}) := by
    ext x
    simp only [mem_ofPred_eq, eval_equation, sub_eq_zero, mem_preimage, mem_singleton_iff]
  rwa [he]

omit [Fintype ι] in
theorem continuousOn_restore_curve (base : ι) {a b : ℝ}
    {γ : ℝ → CoordinateSlice.Index base → ℝ} (hγ : ContinuousOn γ (Icc a b)) :
    ContinuousOn (fun t => CoordinateSlice.restore base t (γ t)) (Icc a b) := by
  apply continuousOn_pi.mpr
  intro i
  by_cases hi : i = base
  · simp only [CoordinateSlice.restore, dite_eq_left hi]
    convert (continuous_id.continuousOn : ContinuousOn (id : ℝ → ℝ) (Icc a b)) using 1
    rfl
  · simpa only [CoordinateSlice.restore, dite_eq_right hi, Function.comp_def] using
      (continuous_apply (⟨i, hi⟩ : CoordinateSlice.Index base)).comp_continuousOn hγ

/-- No regularity or compactness of the endpoint slices is assumed. The
index is the actual critical root fiber at the sample coordinate. -/
theorem exists_arcs (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x))
    (hregular : ∀ x : ι → ℝ, p.eval x = c →
      Function.Surjective (fderiv ℝ (fun y => p.eval y) x)) :
    ∃ u : DirectionIndex pivot → ℕ, ∃ r : Polynomial ℝ,
      r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
      ∀ (a b : ℝ) (t₀ : Ioo a b), (∀ t ∈ Ioo a b, r.eval t ≠ 0) →
        Finite (RootBranches.Index (system p base c pivot u) a b t₀) ∧
        ∃ arc : RootBranches.Index (system p base c pivot u) a b t₀ → ℝ →
            CoordinateSlice.Index base → ℝ,
          (∀ j, arc j t₀.val = j.val.val.val.2) ∧
          (∀ j, ContinuousOn (arc j) (Icc a b)) ∧
          (∀ j t, t ∈ Icc a b → system p base c pivot u (t, arc j t) = 0) ∧
          (∀ t : Ioo a b, ∀ x, system p base c pivot u (t.val, x) = 0 ↔
            ∃! j, arc j t.val = x) ∧
          ∀ j t, t ∈ Icc a b → p.eval (CoordinateSlice.restore base t (arc j t)) = c := by
  obtain ⟨u, r, hr, _, P, hP, hnative⟩ :=
    ParameterizedCriticalBranches.exists_regular_system (equation p base c) pivot
  obtain ⟨d, hd, _, hcombined⟩ := PolynomialHypersurfaceSweep.exists_exceptional p base c hregular
  refine ⟨u, r * d, mul_ne_zero hr hd,
    Polynomial.finite_setOfPred_isRoot (mul_ne_zero hr hd), ?_⟩
  intro a b t₀ havoid
  have hfac (t : ℝ) (ht : t ∈ Ioo a b) : r.eval t ≠ 0 ∧ d.eval t ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [Polynomial.eval_mul] using havoid t ht)
  let f := system p base c pivot u
  have hproper : IsProperMap (RootProjection.projection f) := isProperMap p base c pivot u hp
  have hf (z : RootProjection.Space f) (_ : RootProjection.projection f z ∈ Ioo a b) :
      ContDiffAt ℝ 1 f z.val := (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  have hgood (z : RootProjection.Space f) (hz : RootProjection.projection f z ∈ Ioo a b) :=
    (hnative z.val.1 (hfac _ hz).1).2 z.val.2 z.property
      (slice_regular p base c z.val.1 z.val.2
        (hcombined _ (root_level p base c pivot u _ _ z.property)
          (by simpa only [CoordinateSlice.restore_base] using (hfac z.val.1 hz).2)))
  have hJac (z : RootProjection.Space f) (hz : RootProjection.projection f z ∈ Ioo a b) :
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ (CoordinateSlice.Index base → ℝ)).IsInvertible :=
    (PolynomialRootFamily.isInvertible_iff _ z.val).mpr (hgood z hz).1
  refine ⟨RootBranches.finite_index f a b t₀ hproper hf hJac, ?_⟩
  obtain ⟨arc, hanchor, hc, hroot, hcomplete, _⟩ := RegularRootArcs.exists_anchored_arcs
    f a b t₀ (PolynomialRootFamily.contDiff_value _ 1).continuous hproper hf hJac P hP
      (fun z hz => (hgood z hz).2)
  exact ⟨arc, hanchor, hc, hroot, hcomplete,
    fun j t ht => root_level p base c pivot u t (arc j t) (hroot j t ht)⟩

end LeanCanny.Connectivity.CoordinateCriticalArcs
