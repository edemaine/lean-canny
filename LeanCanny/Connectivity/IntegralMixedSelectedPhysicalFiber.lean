/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
public import LeanCanny.Connectivity.ClopenPathCover
/-! # Exact physical fibers over the selected parent homomorphism

Free critical rows and the actual frozen equations describe the same
physical tuples as the selected mixed-system fibers, homeomorphically.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedCriticalArcs
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

def physical (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) : Set (Fin (n+1) → ℝ) :=
  {y | (∀ i, i.val < r.critical.offset.val → ((data x hm r.critical).scales i : ℝ) * y i = heightValue x r φ t i) ∧
    ∀ j, (IntegralMixedSweepRows.integerRow P r j).eval₂ (Int.castRingHom ℝ) y = 0}

def freeCoordinates (r : Rule n) (y : Fin (n+1) → ℝ) (j : Free r) :=
  y (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)

theorem reconstruct (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (y : Fin (n+1) → ℝ)
    (hy : ∀ i, i.val < r.critical.offset.val → ((data x hm r.critical).scales i : ℝ) * y i = heightValue x r φ t i) :
    IntegralMixedSweepRows.point x hm r φ t (freeCoordinates r y) = y := by
  apply CoordinateFrozenCriticalElimination.point_eq (evaluation x φ t) (data x hm r.critical).scales
    (data x hm r.critical).scales_ne (heights x r) r.critical.offset.val (fit r) y
  intro i hi
  rw [evaluation_heights]
  exact hy i hi

theorem free_point (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (z : Free r → ℝ) :
    freeCoordinates r (IntegralMixedSweepRows.point x hm r φ t z) = z := by
  funext j
  exact point_free x hm r φ t z j

theorem point_continuous (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    Continuous (fun w : ℝ × (Free r → ℝ) => IntegralMixedSweepRows.point x hm r φ w.1 w.2) := by
  apply continuous_pi
  intro i
  unfold IntegralMixedSweepRows.point ClearedCoordinateBlock.point
  split_ifs with hi
  · exact (continuous_apply _).comp continuous_snd
  · have H := (((IntegralMixedSweepRows.numerators x hm r i.val).map φ.toRingHom).continuous.comp
      (continuous_fst : Continuous (Prod.fst : ℝ × (Free r → ℝ) → ℝ))).div_const (IntegralMixedSweepRows.denominator x hm r : ℝ)
    simp only [evaluation, RingHom.comp_apply, map_intCast]
    convert H using 1
    rfl

noncomputable def homeomorph (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) : Fiber x hm r φ t ≃ₜ physical x hm r φ t where
  toFun z := ⟨IntegralMixedSweepRows.point x hm r φ t z.val,
    fun i hi => point_frozen x hm r φ t z.val i hi,
    (original_zero_iff x hm r φ t z.val).mp z.property⟩
  invFun y := ⟨freeCoordinates r y.val, (original_zero_iff x hm r φ t (freeCoordinates r y.val)).mpr (by
    rw [reconstruct x hm r φ t y.val y.property.1]
    exact y.property.2)⟩
  left_inv z := Subtype.ext (free_point x hm r φ t z.val)
  right_inv y := Subtype.ext (reconstruct x hm r φ t y.val y.property.1)
  continuous_toFun := ((point_continuous x hm r φ).comp
    (continuous_const.prodMk continuous_subtype_val)).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    exact (continuous_apply (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)).comp
      (continuous_subtype_val : Continuous (Subtype.val : physical x hm r φ t → (Fin (n+1) → ℝ)))

theorem finite_fiber (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) [Finite (Fiber x hm r φ t)] : Finite (physical x hm r φ t) :=
  Finite.of_equiv _ (homeomorph x hm r φ t).toEquiv

noncomputable def cover {J : Type} (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (C : ClopenPathCover (Fiber x hm r φ t) J) :
    ClopenPathCover (physical x hm r φ t) J := C.comap (homeomorph x hm r φ t).symm

end LeanCanny.Connectivity.IntegralMixedSelectedPhysicalFiber
