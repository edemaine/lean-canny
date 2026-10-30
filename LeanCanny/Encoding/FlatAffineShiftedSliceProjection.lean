/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftedSliceCompact
public import LeanCanny.Geometry.RegularComponentTransport

/-! # The actual varying slices are fibers of a proper height projection

Remove the varied constraint while keeping the exact frozen ancestry. The
remaining source slice is compact. Its continuous height difference is
proper, and its fibers are precisely the original shifted slices.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineShiftedSlice
open Set LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity stageWidth)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def coarseSlice (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) : Set (Fin (arity F u) → ℝ) :=
  {y | (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y = 0 ∧
    ∀ j ∈ (FlatAffineFullSourceTower.free F u (F.depth u)).erase h,
      (∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i) =
        (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))}

noncomputable def heightValue (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (y : Fin (arity F u) → ℝ) : ℝ :=
  (∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) h.succ i : ℝ) * y i) -
    (FlatAffineFullSourceTower.level F u (F.depth u) h).polynomial.eval₂ (Int.castRingHom ℝ)
      (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))

noncomputable def projection (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) : coarseSlice F u x h → ℝ := fun y => heightValue F u x h y.val

theorem continuous_heightValue (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) : Continuous (heightValue F u x h) :=
  (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).sub continuous_const

theorem coarse_compact (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) : IsCompact (coarseSlice F u x h) := by
  have HP : IsCompact {y : Fin (arity F u) → ℝ |
      (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y = 0} := by
    have H := (BoundedFullCriticalSamples.source_proper F.source u).isCompact_preimage (isCompact_singleton (x := (0 : ℝ)))
    have HE : (fun y : Fin (F.source.dim u + 4) → ℝ => (BoundedFullCriticalSamples.realPolynomial F.source u).eval y) =
        (fun y => (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y) := by
      funext y
      exact MvPolynomial.eval_map (Int.castRingHom ℝ) y (BoundedFullCriticalSamples.polynomial F.source u)
    rw [HE] at H
    exact H
  have HC : IsClosed {y : Fin (arity F u) → ℝ | ∀ j ∈ (FlatAffineFullSourceTower.free F u (F.depth u)).erase h,
      (∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i) =
        (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (x.val ∘ TriangularPolynomialIndexing.enumerate (stageWidth F u) (F.depth u))} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro _
    exact isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))) continuous_const
  exact HP.inter_right HC

theorem projection_proper (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) : IsProperMap (projection F u x h) := by
  let : CompactSpace (coarseSlice F u x h) := isCompact_iff_compactSpace.mp (coarse_compact F u x h)
  exact ((continuous_heightValue F u x h).comp continuous_subtype_val).isProperMap

theorem slice_iff_fiber (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u))
    (v : ℝ) (y : Fin (arity F u) → ℝ) :
    y ∈ slice F u x h v ↔ y ∈ coarseSlice F u x h ∧ heightValue F u x h y = v := by
  constructor
  · intro hy
    refine ⟨⟨hy.1, ?_⟩, ?_⟩
    · intro j hj
      have HJ := Finset.mem_erase.mp hj
      have HL := hy.2 j HJ.2
      simpa only [ite_eq_right HJ.1, add_zero] using HL
    · have HL := hy.2 h hs
      simp only [ite_true] at HL
      change _ - _ = _
      linarith
  · rintro ⟨hy, hv⟩
    refine ⟨hy.1, ?_⟩
    intro j hj
    by_cases he : j = h
    · subst j
      simp only [ite_true]
      change _ - _ = _ at hv
      linarith
    · have HL := hy.2 j (Finset.mem_erase.mpr ⟨he, hj⟩)
      simpa only [ite_eq_right he, add_zero] using HL

theorem image_fiber (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ) :
    Subtype.val '' ((projection F u x h) ⁻¹' {v}) = slice F u x h v := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (slice_iff_fiber F u x h hs v z.val).mpr ⟨z.property, hz⟩
  · intro hy
    obtain ⟨hz, hv⟩ := (slice_iff_fiber F u x h hs v y).mp hy
    exact ⟨⟨y, hz⟩, hv, rfl⟩

theorem joined_fiber_iff (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (h : Fin (arity F u)) (hs : h ∈ FlatAffineFullSourceTower.free F u (F.depth u)) (v : ℝ)
    (y z : coarseSlice F u x h) (hy : projection F u x h y = v) (hz : projection F u x h z = v) :
    JoinedIn ((projection F u x h) ⁻¹' {v}) y z ↔ JoinedIn (slice F u x h v) y.val z.val := by
  have HE := Topology.IsEmbedding.subtypeVal.isInducing.joinedIn_image
    (F := (projection F u x h) ⁻¹' {v}) (x := y) (y := z) hy hz
  rw [image_fiber F u x h hs v] at HE
  exact HE.symm

end LeanCanny.Encoding.FlatAffineShiftedSlice
