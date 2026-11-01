/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.WeakBooleanWitness
/-! # Paths in an attenuated circular atom, including zero and negative inactive atoms -/
@[expose] public section
namespace LeanCanny.Geometry.ScaledCirclePaths
open CircularWitness Set Metric
open scoped Classical

noncomputable def center (a l : ℝ) : Plane := if 0<a then (l/Real.sqrt a) • unit else 0

theorem continuous_center (a : ℝ) : Continuous (center a) := by
  unfold center
  split_ifs
  · exact (continuous_id.div_const _).smul continuous_const
  · exact continuous_const

theorem inactive {a l : ℝ} {w : Plane} (hl : 0≤l) (he : a*‖w‖^2=l^2) (ha : a≤0) : l=0 := by
  have HN := mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg ‖w‖)
  nlinarith

theorem center_equation (a l : ℝ) (hz : a≤0 → l=0) : a*‖center a l‖^2=l^2 := by
  by_cases HA : 0<a
  · have HD : Real.sqrt a≠0 := (Real.sqrt_pos.mpr HA).ne'
    simp only [center,ite_eq_left HA,norm_smul,unit_norm,mul_one,Real.norm_eq_abs,sq_abs,div_pow,
      Real.sq_sqrt HA.le]
    field_simp
  · rw [center,ite_eq_right HA,hz (le_of_not_gt HA)]
    simp

 theorem atom_path (a l : ℝ) (w : Plane) (hl : 0≤l) (he : a*‖w‖^2=l^2) :
    ∃ γ : Path w (center a l), ∀ t, a*‖γ t‖^2=l^2 := by
  by_cases HA : 0<a
  · have HR : 0≤l/Real.sqrt a := div_nonneg hl (Real.sqrt_nonneg a)
    have HC : ‖center a l‖=l/Real.sqrt a := by
      simp only [center,ite_eq_left HA,norm_smul,unit_norm,mul_one,Real.norm_eq_abs,abs_of_nonneg HR]
    have HE := center_equation a l (fun H => (not_lt_of_ge H HA).elim)
    have HW : ‖w‖=l/Real.sqrt a := by
      rw [← HC]
      have Hsq : ‖w‖^2=‖center a l‖^2 := by nlinarith
      nlinarith [norm_nonneg w,norm_nonneg (center a l)]
    have HD : 1 < Module.rank ℝ Plane := by rw [← Module.finrank_eq_rank]; norm_num
    have HS := isPathConnected_sphere HD (0 : Plane) HR
    obtain ⟨γ,Hγ⟩ := HS.joinedIn w (by simpa only [mem_sphere,dist_zero_right] using HW)
      (center a l) (by simpa only [mem_sphere,dist_zero_right] using HC)
    refine ⟨γ,fun t => ?_⟩
    have HT : ‖γ t‖=l/Real.sqrt a := by simpa only [mem_sphere,dist_zero_right] using Hγ t
    rw [HT,← HW]
    exact he
  · have HZ := inactive hl he (le_of_not_gt HA)
    rw [center,ite_eq_right HA]
    by_cases H0 : a=0
    · refine ⟨Path.segment w 0,fun _ => ?_⟩
      rw [H0,HZ]
      simp
    · have HW : w=0 := by
        have HE0 : a*‖w‖^2=0 := by rw [he,HZ]; norm_num
        have HS := (mul_eq_zero.mp HE0).resolve_left H0
        exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])
      subst w
      exact ⟨Path.refl 0,fun _ => by simp [HZ]⟩

end LeanCanny.Geometry.ScaledCirclePaths
