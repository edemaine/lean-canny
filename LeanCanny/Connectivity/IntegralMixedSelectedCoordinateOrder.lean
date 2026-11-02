/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedGridArcs
public import LeanCanny.Geometry.RootCurveOrder
public import LeanCanny.Geometry.RootSlabEquivalence

/-! # Actual selected coordinate order persists on each retained interval

The scalar covering is built from the validated selected PSC auxiliary.
Properness comes from the original selected polynomial's fixed nonzero
leading coefficient. Neither an absolute norm fiber nor a supplied covering
or branch-order hypothesis is used.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateOrder
open Set LeanCanny.Algebra LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def scalar (p : Polynomial (Polynomial ℝ)) : ℝ×(Fin 1→ℝ)→(Fin 1→ℝ) :=
  PolynomialRootFamily.value (UnivariateRootFamily.diagonal (fun _ : Fin 1=>p))

theorem scalar_zero_iff (p : Polynomial (Polynomial ℝ)) (t : ℝ) (a : Fin 1→ℝ) :
    scalar p (t,a)=0↔p.eval₂ (Polynomial.evalRingHom t) (a 0)=0 := by
  constructor
  · intro H
    simpa only [scalar,UnivariateRootFamily.value_diagonal,Pi.zero_apply] using congrFun H 0
  · intro H
    funext i
    simpa only [scalar,UnivariateRootFamily.value_diagonal,Fin.eq_zero i,Pi.zero_apply] using H

theorem covering (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (j : Free r)
    (c : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : IntegralMixedCoordinateSquarefree.Valid x hm r j φ c) (a b : ℝ)
    (havoid : ∀ t∈Ioo a b,(IntegralMixedCoordinateSquarefree.exceptional x hm r j c).eval₂ φ.toRingHom t≠0) :
    IsCoveringMap (RootBranches.projection (scalar
      ((IntegralMixedCoordinateSquarefree.auxiliary x hm r j c).map (Polynomial.mapRingHom φ.toRingHom))) a b) := by
  let p:=(selected x hm r j φ)
  let q:=(IntegralMixedCoordinateSquarefree.auxiliary x hm r j c).map (Polynomial.mapRingHom φ.toRingHom)
  have HP : IsProperMap (RootBranches.projection (scalar p) a b):=
    PolynomialCoordinateProper.proper_restriction (fun _ : Fin 1=>p) (Ioo a b)
      (fun _ t _=>selected_leading x hm r φ j t)
  have HE (t : ℝ) (ht : t∈Ioo a b) (y : Fin 1→ℝ) : scalar p (t,y)=0↔scalar q (t,y)=0 := by
    rw [scalar_zero_iff,scalar_zero_iff]
    rw [Polynomial.eval₂_map]
    exact (IntegralMixedCoordinateSquarefree.roots_away x hm r j φ c hc t (y 0) (havoid t ht)).symm
  apply LocalProperRootBranches.covering _ a b (RootSlabEquivalence.proper_restriction (scalar p) (scalar q) (Ioo a b) HE HP)
  · intro z _
    exact (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  · intro z hz
    apply UnivariateRootFamily.regular_diagonal _ z.val.1 z.val.2 _ z.property
    intro _
    rw [Polynomial.map_map]
    exact IntegralMixedCoordinateSquarefree.separable_away x hm r j φ c hc z.val.1 (havoid _ hz)

theorem comparison (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (j : Free r)
    (c : Fin (IntegralMixedCoordinateSquarefree.coordinateDegree P r))
    (hc : IntegralMixedCoordinateSquarefree.Valid x hm r j φ c) {a b : ℝ}
    (havoid : ∀ t∈Ioo a b,(IntegralMixedCoordinateSquarefree.exceptional x hm r j c).eval₂ φ.toRingHom t≠0)
    (f g : C(Ioo a b,Free r→ℝ))
    (hf : ∀ t,(selected x hm r j φ).eval₂ (Polynomial.evalRingHom t.val) (f t j)=0)
    (hg : ∀ t,(selected x hm r j φ).eval₂ (Polynomial.evalRingHom t.val) (g t j)=0)
    (s t : Ioo a b) : (f s j=g s j↔f t j=g t j) ∧ (f s j<g s j↔f t j<g t j) := by
  apply RootBranches.coordinate_comparison_iff _ (covering x hm r φ j c hc a b havoid) f g j _ _ s t
  · intro u
    rw [scalar_zero_iff,Polynomial.eval₂_map]
    exact (IntegralMixedCoordinateSquarefree.roots_away x hm r j φ c hc u.val (f u j) (havoid _ u.property)).mpr (hf u)
  · intro u
    rw [scalar_zero_iff,Polynomial.eval₂_map]
    exact (IntegralMixedCoordinateSquarefree.roots_away x hm r j φ c hc u.val (g u j) (havoid _ u.property)).mpr (hg u)

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateOrder
