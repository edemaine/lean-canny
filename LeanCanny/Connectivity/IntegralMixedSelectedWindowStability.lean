/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateWindow
/-! # Ordered window stabilization removes the endpoint near quantifiers

The smaller displacement stays on the prescribed side of the same interval.
Only monotonicity of the coordinate window in its tolerance is used.
-/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedWindowStability
open LeanCanny.Algebra LeanCanny.Geometry Set Polynomial
open IntegralMixedSelectedCoordinateWindow
open scoped Classical

private theorem window_mono (p : ℝ[X]) (code : ℕ) (y ε ε' : ℝ) (he : ε≤ε') :
    Window p code y ε→Window p code y ε' :=by
  intro H
  obtain ⟨z,hz,hr,hd⟩:=window_iff p code y ε |>.mp H
  exact (window_iff p code y ε').mpr ⟨z,hz,hr,hd.trans_le he⟩

theorem endpoint_iff_of_stable (p : ℝ→ℝ[X]) {a b : ℝ} (hab : a<b) (right : Bool)
    (code : ℕ) (y : ℝ) (B : Prop)
    (H : ∃ η : ℝ,0<η ∧ ∀ ε : ℝ,0<ε→ε<η→∃ ζ : ℝ,0<ζ ∧
      ∀ δ : ℝ,0<δ→δ<ζ→(Window (p (if right then b-δ else a+δ)) code y ε↔B)) :
    (∀ ε : ℝ,0<ε→∀ Δ : ℝ,0<Δ→∃ t : ℝ,t∈Ioo a b ∧
      dist t (if right then b else a)<Δ ∧ Window (p t) code y ε)↔B :=by
  obtain ⟨η,hη,H⟩:=H
  constructor
  · intro hn
    obtain ⟨ζ,hζ,Hz⟩:=H (η/2) (by linarith) (by linarith)
    obtain ⟨t,ht,hd,hw⟩:=hn (η/2) (by linarith) ζ hζ
    let δ:=if right then b-t else t-a
    have hδ : 0<δ:=by cases right <;> dsimp [δ] <;> linarith [ht.1,ht.2]
    have hdist : dist t (if right then b else a)=δ :=by
      cases right with
      | false =>
        change dist t a=t-a
        rw [Real.dist_eq,abs_of_pos (sub_pos.mpr ht.1)]
      | true =>
        change dist t b=b-t
        rw [Real.dist_eq,abs_of_neg (sub_neg.mpr ht.2)]
        ring
    have hp : (if right then b-δ else a+δ)=t :=by cases right <;> dsimp [δ] <;> ring
    exact (Hz δ hδ (by rw [←hdist];exact hd)).mp (by rw [hp];exact hw)
  · intro hB ε hε Δ hΔ
    let ε₀:=min ε (η/2)
    have hε₀ : 0<ε₀:=lt_min hε (by linarith)
    have hεη : ε₀<η:=(min_le_right _ _).trans_lt (by linarith)
    obtain ⟨ζ,hζ,Hz⟩:=H ε₀ hε₀ hεη
    let δ:=min Δ (min ζ (b-a))/2
    have hm : 0<min Δ (min ζ (b-a)):=lt_min hΔ (lt_min hζ (sub_pos.mpr hab))
    have hδ : 0<δ:=by dsimp [δ];linarith
    have hlt : δ<min Δ (min ζ (b-a)):=by dsimp [δ];linarith
    have hδΔ : δ<Δ:=hlt.trans_le (min_le_left _ _)
    have hδζ : δ<ζ:=hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hδb : δ<b-a:=hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    refine ⟨if right then b-δ else a+δ,?_,?_,?_⟩
    · cases right <;> dsimp <;> constructor <;> linarith
    · cases right with
      | false =>
        change dist (a+δ) a<Δ
        rw [Real.dist_eq,show a+δ-a=δ by ring,abs_of_pos hδ]
        exact hδΔ
      | true =>
        change dist (b-δ) b<Δ
        rw [Real.dist_eq,show b-δ-b= -δ by ring,abs_neg,abs_of_pos hδ]
        exact hδΔ
    · exact window_mono _ code y ε₀ ε (min_le_left _ _) ((Hz δ hδ hδζ).mpr hB)


theorem selected_near_iff_of_stable {n S Bm m : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P S Bm m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) {a b : ℝ} (hab : a<b) (right : Bool)
    (i : IntegralMixedSelectedGeometry.Free r) (code : ℕ) (y : ℝ) (B : Prop)
    (H : ∃ η : ℝ,0<η ∧ ∀ ε : ℝ,0<ε→ε<η→∃ ζ : ℝ,0<ζ ∧
      ∀ δ : ℝ,0<δ→δ<ζ→
        (Window (IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ
          (if right then b-δ else a+δ) i) code y ε↔B)) :
    IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b (if right then b else a) i code y↔B :=by
  rw [near_iff_counts]
  simp_rw [scaled_window_iff]
  exact endpoint_iff_of_stable (fun t=>IntegralMixedFrozenFrameSectionCode.polynomial x hm r φ t i) hab right code y B H

end LeanCanny.Connectivity.IntegralMixedSelectedWindowStability
