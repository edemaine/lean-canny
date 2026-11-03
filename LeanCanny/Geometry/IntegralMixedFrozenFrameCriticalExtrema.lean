/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalValues
public import LeanCanny.Geometry.IntegralMixedFrozenFrameProjection

/-! # Attained coordinate extrema are actual critical heights

Both signs of the objective use the singular-safe affine critical theorem.
No regularity of the frozen slice or component-selection premise is needed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory MvPolynomial Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

/-- A signed coordinate maximum has vanishing other free partials, including
at singular points of the constrained source. -/
theorem free_partials_of_signed_max (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen)
    (b : ℝ) (hb : b≠0) (z : Fin (n+1)→ℝ) (hz : z∈slice P F values)
    (hmax : IsLocalMaxOn (fun y : Fin (n+1)→ℝ=>b*y h) (slice P F values) z) :
    ∀ i,i∉F.frozen→i≠h→
      (pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) z=0 := by
  let q : Fin (n+1)→ℝ:=fun i=>(F.scales i:ℝ)
  let a:=PhysicalPowerCriticalRows.coordinateNormals b q h
  let H : Fin (n+1)→ℝ:=fun i=>(F.heights i).evaluate values
  let p:=IntegralMixedSelectedComponentSampling.polynomial P
  have HE : {y : Fin (n+1)→ℝ | p.eval₂ (RingHom.id ℝ) y=0 ∧
      ∀ j∈F.frozen,∑ i,(RingHom.id ℝ) (a j.succ i)*y i=(X j).eval₂ (RingHom.id ℝ) H}=
      slice P F values := by
    ext y
    simp only [p,IntegralMixedSelectedComponentSampling.polynomial_eval,RingHom.id_apply,eval₂_X]
    apply and_congr_right
    intro _
    constructor <;> intro HY j hj
    · have HH:=HY j hj
      simpa [a,PhysicalPowerCriticalRows.coordinateNormals,q,H,eq_comm] using HH
    · simpa [a,PhysicalPowerCriticalRows.coordinateNormals,q,H,eq_comm] using HY j hj
  have Hproj : (fun y=>ProjectionCritical.projection (fun i=>(RingHom.id ℝ) (a 0 i)) y)=
      (fun y : Fin (n+1)→ℝ=>b*y h) := by
    funext y
    simp [ProjectionCritical.projection,a,PhysicalPowerCriticalRows.coordinateNormals]
  have Hheights (c : F.frozen→ℝ)
      (HC : ∀ i,∑ j : F.frozen,c j*(RingHom.id ℝ) (a j.val.succ i)=0) : ∀ j,c j=0 := by
    apply IntegralMixedSelectedComponentSampling.normal_independent F.frozen q
      (fun i=>Int.cast_ne_zero.mpr (F.scales_ne_zero i)) h c
    simpa only [a,PhysicalPowerCriticalRows.coordinateNormals,Fin.cons_succ,RingHom.id_apply] using HC
  have Hobjective : ¬∃ c : F.frozen→ℝ,∀ i,(RingHom.id ℝ) (a 0 i)=
      ∑ j : F.frozen,c j*(RingHom.id ℝ) (a j.val.succ i) := by
    rintro ⟨c,HC⟩
    have HH:=HC h
    have HJ (j : F.frozen) : h≠j.val:=fun hj=>hh (hj.symm ▸ j.property)
    simp only [a,PhysicalPowerCriticalRows.coordinateNormals,Fin.cons_zero,Fin.cons_succ,
      RingHom.id_apply,ite_true,ite_eq_right (HJ _),mul_zero,Finset.sum_const_zero] at HH
    exact hb HH
  obtain ⟨mu,HM⟩:=FlatAffineSingularCriticalRoot.exists_stage_root_at_max (RingHom.id ℝ)
    p F.frozen a (fun j=>X j) H z
    (by rw [IntegralMixedSelectedComponentSampling.polynomial_eval]; exact hz.1)
    (fun j hj=>by
      simpa [a,PhysicalPowerCriticalRows.coordinateNormals,q,H,eq_comm] using hz.2 j hj)
    (by rw [HE]; simpa only [Hproj] using hmax) Hheights Hobjective
  have HG:=(FlatAffineCriticalStage.roots_iff (RingHom.id ℝ) p F.frozen a (fun j=>X j)
    (Sum.elim H (Sum.elim z mu))).mp HM
  intro i hi hih
  have HP:=HG.2.2.1 i
  have HU:=HG.2.2.2 i hi
  change mu i.succ=0 at HU
  change (pderiv i p).eval₂ (RingHom.id ℝ) z=∑ j,(RingHom.id ℝ) (a j i)*mu j at HP
  have HS:=PhysicalPowerCriticalRows.normal_power_sum (RingHom.id ℝ) b q h i mu 1
  simp only [RingHom.id_apply,pow_one,ite_eq_right hih,HU,mul_zero,add_zero] at HS
  have HZ : (pderiv i p).eval₂ (RingHom.id ℝ) z=0:=
    HP.trans (by simpa only [a,RingHom.id_apply] using HS)
  simpa only [p,IntegralMixedSelectedComponentSampling.polynomial,pderiv_map,eval₂_map,RingHom.id_comp] using HZ

theorem critical_height_of_isMaxOn (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (z : Fin (n+1)→ℝ) (hz : z∈slice P F values)
    (hzmax : IsMaxOn (fun y=>y h) (slice P F values) z) :
    z h∈realCriticalValues P (line F h) values h := by
  apply (line_realCriticalValues_iff P F values h hh HF _).mpr
  refine ⟨z,hz,rfl,?_⟩
  apply free_partials_of_signed_max P F values h hh 1 one_ne_zero z hz
  simpa only [one_mul] using hzmax.isLocalMaxOn

theorem critical_height_of_isMinOn (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (z : Fin (n+1)→ℝ) (hz : z∈slice P F values)
    (hzmin : IsMinOn (fun y=>y h) (slice P F values) z) :
    z h∈realCriticalValues P (line F h) values h := by
  apply (line_realCriticalValues_iff P F values h hh HF _).mpr
  refine ⟨z,hz,rfl,?_⟩
  apply free_partials_of_signed_max P F values h hh (-1) (by norm_num) z hz
  simpa only [neg_one_mul] using hzmin.neg.isLocalMaxOn

/-- The enclosing values are attained at actual points of the original slice. -/
theorem exists_critical_extrema (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (hne : (slice P F values).Nonempty) :
    ∃ lo hi : Fin (n+1)→ℝ,lo∈slice P F values ∧ hi∈slice P F values ∧
      lo h∈realCriticalValues P (line F h) values h ∧
      hi h∈realCriticalValues P (line F h) values h ∧
      ∀ y∈slice P F values,lo h≤y h ∧ y h≤hi h := by
  have HC : IsCompact (slice P F values):=
    (hp.isCompact_preimage (isCompact_singleton : IsCompact ({0} : Set ℝ))).of_isClosed_subset
      (slice_closed P F values) (fun y hy=>hy.1)
  obtain ⟨lo,Hlo,Hmin⟩:=HC.exists_isMinOn hne (continuous_apply h).continuousOn
  obtain ⟨hi,Hhi,Hmax⟩:=HC.exists_isMaxOn hne (continuous_apply h).continuousOn
  exact ⟨lo,hi,Hlo,Hhi,critical_height_of_isMinOn P F values h hh HF lo Hlo Hmin,
    critical_height_of_isMaxOn P F values h hh HF hi Hhi Hmax,
    fun y hy=>⟨Hmin hy,Hmax hy⟩⟩

end LeanCanny.Geometry.IntegralMixedFrozenFrame
