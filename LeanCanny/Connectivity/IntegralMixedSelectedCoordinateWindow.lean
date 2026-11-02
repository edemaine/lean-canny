/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.OrderedRealRootWindow
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateEndpoint
/-! # Selected-coordinate endpoint tests through two scalar root counts

The window test has no physical-fiber quantifier. Its real roots use the
same selected old hom as the validated physical midpoint branch.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow
open Set Polynomial LeanCanny.Algebra LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def Window (p : ℝ[X]) (code : ℕ) (y ε : ℝ) : Prop :=
  p.roots.toFinset.card≤code+RootSignQueries.signCount p.roots.toFinset
    (fun _ : Fin 1=>X-C (y-ε)) (fun _=>SignType.pos) ∧
  code<RootSignQueries.signCount p.roots.toFinset
    (fun _ : Fin 1=>X-C (y+ε)) (fun _=>SignType.neg)

theorem window_iff (p : ℝ[X]) (code : ℕ) (y ε : ℝ) :
    Window p code y ε↔∃ z∈p.roots.toFinset,
      OrderedRealRootWindow.rank p.roots.toFinset z=code ∧ dist z y<ε := by
  rw [Window,←OrderedRealRootWindow.exists_rank_window_signCounts]
  apply exists_congr
  intro z
  apply and_congr_right'
  apply and_congr_right'
  rw [Real.dist_eq,abs_lt]
  constructor <;> intro H <;> constructor <;> linarith [H.1,H.2]

theorem total_query (p : ℝ[X]) :
    RootSignQueries.tarskiQuery p 1=(p.roots.toFinset.card : ℤ) := by
  simp only [RootSignQueries.tarskiQuery,RootSignQueries.signSum,Polynomial.eval_one,sign_one,
    SignType.coe_one,Finset.sum_const,nsmul_eq_mul,mul_one]

noncomputable def ScaledWindow (p : ℝ[X]) (code : ℕ) (y ε : ℝ) : Prop :=
  2*RootSignQueries.tarskiQuery p 1≤2*(code : ℤ)+RootSignQueries.scaledRootCount p
    (fun _ : Fin 1=>X-C (y-ε)) (fun _=>SignType.pos) ∧
  2*(code : ℤ)<RootSignQueries.scaledRootCount p
    (fun _ : Fin 1=>X-C (y+ε)) (fun _=>SignType.neg)

theorem scaled_window_iff (p : ℝ[X]) (code : ℕ) (y ε : ℝ) :
    ScaledWindow p code y ε↔Window p code y ε := by
  simp only [ScaledWindow,Window,total_query,RootSignQueries.scaledRootCount_eq,
    Fintype.card_fin,pow_one]
  omega

theorem near_iff_counts (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint : ℝ) (i : Free r) (code : ℕ) (y : ℝ) :
    IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b endpoint i code y↔
      ∀ ε : ℝ,0<ε→∀ δ : ℝ,0<δ→∃ t : ℝ,t∈Ioo a b ∧ dist t endpoint<δ ∧
        ScaledWindow (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t i) code y ε := by
  unfold IntegralMixedSelectedCoordinateEndpoint.Near
  apply forall_congr'
  intro ε
  apply forall_congr'
  intro _
  apply forall_congr'
  intro δ
  apply forall_congr'
  intro _
  apply exists_congr
  intro t
  apply and_congr_right'
  apply and_congr_right'
  rw [scaled_window_iff,window_iff]
  rfl

end LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow
