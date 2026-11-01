/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.SquaredDistanceFibers
public import LeanCanny.Connectivity.AccessibleArc
/-! # A radial branch reaches its prescribed original center

Only the projected tuple must converge. Auxiliary native witnesses may have
multiple limits; no lifting of a chosen absolute root is used.
-/
@[expose] public section
namespace LeanCanny.Geometry.RadialArcAccess
open Set Filter
open scoped Topology
variable {n : ℕ}

theorem tendsto_center (center : Fin n → ℝ) (b : ℝ) (hb : 0 < b)
    (f : ℝ → Fin n → ℝ) (hr : ∀ t∈Ioo 0 b, SquaredDistanceFibers.value center (f t)=t) :
    Tendsto f (𝓝[>] 0) (𝓝 center) := by
  let E := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm
  have HE : (fun t => ‖E (f t)-E center‖)=ᶠ[𝓝[>] 0] Real.sqrt := by
    filter_upwards [Ioo_mem_nhdsGT hb] with t ht
    have H : ‖E (f t)-E center‖^2=t := (SquaredDistanceFibers.norm_sq center (f t)).trans (hr t ht)
    exact (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt H)
  have HS : Tendsto Real.sqrt (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (Real.sqrt 0)))
  have HN : Tendsto (fun t => E (f t)) (𝓝[>] 0) (𝓝 (E center)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (HS.congr' HE.symm)
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using E.symm.continuous.continuousAt.tendsto.comp HN

theorem joined_center (center : Fin n → ℝ) (b : ℝ) (f : ℝ → Fin n → ℝ)
    (hf : ContinuousOn f (Ioo 0 b))
    (hr : ∀ t∈Ioo 0 b, SquaredDistanceFibers.value center (f t)=t)
    (s : Set (Fin n → ℝ)) (hs : ∀ t∈Ioo 0 b, f t∈s) (a : ℝ) (ha : a∈Ioo 0 b) :
    JoinedIn (insert center s) center (f a) := by
  obtain ⟨u,hau,hub⟩ := exists_between ha.2
  have hu : u∈Ioo 0 b := ⟨ha.1.trans hau,hub⟩
  have HU : ContinuousOn f (Ioo 0 u) := hf.mono (Ioo_subset_Ioo le_rfl hub.le)
  have HL := tendsto_center center b (ha.1.trans ha.2) f hr
  have HR : Tendsto f (𝓝[<] u) (𝓝 (f u)) :=
    ((hf u hu).continuousAt (Ioo_mem_nhds hu.1 hu.2)).tendsto.mono_left nhdsWithin_le_nhds
  let g := extendFrom (Ioo 0 u) f
  have HG : ContinuousOn g (Icc 0 u) := continuousOn_Icc_extendFrom_Ioo HU HL HR
  have H0 : g 0=center := extendFrom_eq (by rw [closure_Ioo (ne_of_lt hu.1)]; exact ⟨le_rfl,hu.1.le⟩)
    (HL.mono_left (nhdsWithin_mono _ Ioo_subset_Ioi_self))
  have HI : EqOn g f (Ioo 0 u) := extendFrom_extends HU
  have HP := (LeanCanny.Connectivity.FrontierCover.joinedIn_insert_Ioo
    (x:=0) (y:=a) ⟨le_rfl,hu.1.le⟩ ⟨ha.1,hau⟩).map
      (HG.mono (insert_subset ⟨le_rfl,hu.1.le⟩ Ioo_subset_Icc_self))
  rw [H0,HI ⟨ha.1,hau⟩] at HP
  apply HP.mono
  rintro z ⟨t,ht,rfl⟩
  rcases ht with ht | ht
  · rw [ht,H0]
    exact mem_insert _ _
  · right
    rw [HI ht]
    exact hs t ⟨ht.1,ht.2.trans hub⟩

end LeanCanny.Geometry.RadialArcAccess
