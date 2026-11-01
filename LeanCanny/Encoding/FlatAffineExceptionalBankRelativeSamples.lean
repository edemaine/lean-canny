/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalBankCorrelation
public import LeanCanny.Algebra.IntegralHistoryRelativeCritical
public import LeanCanny.Algebra.IntegralCriticalFactorCeiling

/-! # Relative coordinate births from actual specialized mixed critical roots

The new scalar polynomial is the existing relative critical annihilator over
the constructed coefficient bank. Its degree uses only the free spatial
arity and original source degree. A chosen actual critical root extends
without changing any physical coordinate. Explicit correlation and label
guards identify its physical spatial point with the independent frame slice.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalBankRelativeSamples
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births width)
open FlatAffineExceptionalParentBank (bank criticalData)
open FlatAffineExceptionalBankCorrelation (HistoryIndex JointIndex MatchesFrame Correlated)
open IntegralHistorySampler UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical

theorem relative_degree_cap (F : Inputs) (u : List Bool) (offset k : ℕ)
    (hfit : offset + (k + 1) = arity F u) :
    PurePowerReductionBounds.dimension (k + 1) (FlatAffinePowerControls.degree F u) ≤ 2 ^ width F u :=
  (IntegralCriticalFactorCeiling.dimension_mono (by omega : k + 1 ≤ arity F u) (Nat.le_refl _)).trans
    (FlatAffineExceptionalBankSource.relative_cap F u)

noncomputable def spatialPoint (F : Inputs) (S : ℕ) (u : List Bool)
    (z : (HistoryIndex F u ⊕ Variables (arity F u)) → ℝ) : Fin (arity F u) → ℝ :=
  fun i => z (ambient i) ^ physical S (2 ^ width F u) (births F u)

noncomputable def framePoint (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u a : List Bool)
    (z : (HistoryIndex F u ⊕ Variables (arity F u)) → ℝ) : JointIndex F u → ℝ :=
  Sum.elim (z ∘ Sum.inl) (fun _ => FlatAffineExceptionalSliceFrame.scalar F C h u a)

theorem sample_mem_frame_slice (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineFullSourceTower.free F u (F.depth u))
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (hnormal : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)
    (z : (HistoryIndex F u ⊕ Variables (arity F u)) → ℝ)
    (hz : ∀ j, ((criticalStep (bank F C h S u (hm.trans (Nat.le_succ S))).sampler
      (criticalData F C h S u hm r hr)).rows j).eval₂ (Int.castRingHom ℝ) z = 0)
    (Hframe : MatchesFrame F C h u v a hv (framePoint F C h u a z))
    (Hguard : Correlated F C h S u (hm.trans (Nat.le_succ S)) (framePoint F C h u a z)) :
    spatialPoint F S u z ∈ FlatAffineExceptionalSliceFrame.slice F C h u v a hv := by
  obtain ⟨φ, _hold, Hφ, Hsource, Hheight, _Hgradient, _Hinactive⟩ :=
    criticalStep_roots_interpret (bank F C h S u (hm.trans (Nat.le_succ S))).sampler
      (criticalData F C h S u hm r hr) z hz
  have Hvalues := FlatAffineExceptionalBankCorrelation.recovery_of_correlated F C h S u v a
    (hm.trans (Nat.le_succ S)) hv (framePoint F C h u a z) Hframe Hguard φ Hφ
  have HE := FlatAffineExceptionalParentBank.criticalData_slice F C h S u v a hm r hr hv φ Hvalues hnormal
  rw [← HE]
  refine ⟨?_, Hheight⟩
  exact (congrArg (fun p => p.eval₂ (Int.castRingHom ℝ) (spatialPoint F S u z) = 0)
    (FlatAffineExceptionalParentBank.criticalData_source F C h S u hm r hr)).mp Hsource

/-- Append a selected actual coordinate by a bounded relative scalar birth.
The old critical tuple, including all multipliers and ancestors, is retained. -/
theorem relative_coordinate_extend (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (r : Fin (arity F u)) (hr : r ∉ FlatAffineFullSourceTower.free F u (F.depth u))
    (offset k : ℕ) (hfit : offset + (k + 1) = arity F u)
    (hfrozen : ∀ i, i ∈ FlatAffineFullSourceTower.free F u (F.depth u) ↔ i.val < offset)
    (rLocal jLocal : Fin (k + 1))
    (hfree : r = ClearedCoordinateCritical.freeIndex offset hfit.le rLocal)
    (z : (HistoryIndex F u ⊕ Variables (arity F u)) → ℝ)
    (hz : ∀ l, ((criticalStep (bank F C h S u (hm.trans (Nat.le_succ S))).sampler
      (criticalData F C h S u hm r hr)).rows l).eval₂ (Int.castRingHom ℝ) z = 0) :
    let G := criticalStep (bank F C h S u (hm.trans (Nat.le_succ S))).sampler (criticalData F C h S u hm r hr)
    let p := criticalCandidate (bank F C h S u (hm.trans (Nat.le_succ S))).sampler
      (criticalData F C h S u hm r hr) offset hfit rLocal jLocal
    let d := PurePowerReductionBounds.dimension (k + 1) (FlatAffinePowerControls.degree F u)
    ∃ y : ((HistoryIndex F u ⊕ Variables (arity F u)) ⊕ Unit) → ℝ,
      (∀ l, ((scalarStep G hm (Nat.two_pow_pos (width F u)) p d).rows l).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (scalarStep G hm (Nat.two_pow_pos (width F u)) p d).scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((scalarStep G hm (Nat.two_pow_pos (width F u)) p d).scalarPrefix.basis.generator i) =
          y ((scalarStep G hm (Nat.two_pow_pos (width F u)) p d).scalar i) ^
            weights S (2 ^ width F u) (births F u + 1) i) →
        ψ (PaddedIntegralParameterExtension.numerator (bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.basis p d) /
          ((PaddedIntegralParameterExtension.denominator (bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.basis p d : ℤ) : ℝ) =
          spatialPoint F S u z (ClearedCoordinateCritical.freeIndex offset hfit.le jLocal) :=
  criticalCandidate_real_extend_recover (bank F C h S u (hm.trans (Nat.le_succ S))).sampler
    (criticalData F C h S u hm r hr) (Nat.two_pow_pos (width F u)) (relative_degree_cap F u offset k hfit)
    offset hfit hfrozen rLocal jLocal hfree z hz

end LeanCanny.Encoding.FlatAffineExceptionalBankRelativeSamples
