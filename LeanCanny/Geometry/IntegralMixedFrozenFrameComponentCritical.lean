/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameCriticalExtrema
/-! # Every compact frozen component contains an actual objective-critical point

The sampled point stays in the supplied point's component. No regularity of
the slice, component openness or sample interpretation is a premise.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory MvPolynomial Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem exists_component_objective_critical (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen)
    (hc : IsCompact (slice P F values)) (z : Fin (n+1)→ℝ) (hz : z∈slice P F values) :
    ∃ y : Fin (n+1)→ℝ,y∈connectedComponentIn (slice P F values) z ∧
      ∀ i,i∉F.frozen→i≠h→
        (pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) y=0 :=by
  let q : Fin (n+1)→ℝ:=fun i=>(F.scales i:ℝ)
  let a:=PhysicalPowerCriticalRows.coordinateNormals 2 q h
  let H : Fin (n+1)→ℝ:=fun i=>(F.heights i).evaluate values
  let p:=IntegralMixedSelectedComponentSampling.polynomial P
  let b : Fin (n+1)→MvPolynomial (Fin 0) ℝ:=fun j=>C (H j)
  have HE : {y : Fin (n+1)→ℝ | p.eval₂ (RingHom.id ℝ) y=0 ∧
      ∀ j∈F.frozen,∑ i,(RingHom.id ℝ) (a j.succ i)*y i=
        (b j).eval₂ (RingHom.id ℝ) (fun i=>Fin.elim0 i)}=slice P F values :=by
    ext y
    simp only [p,IntegralMixedSelectedComponentSampling.polynomial_eval,RingHom.id_apply,b,eval₂_C]
    apply and_congr_right
    intro _
    constructor <;> intro HY j hj
    · simpa [a,PhysicalPowerCriticalRows.coordinateNormals,q,H,eq_comm] using HY j hj
    · simpa [a,PhysicalPowerCriticalRows.coordinateNormals,q,H,eq_comm] using HY j hj
  have Hind : ∀ c : F.frozen→ℝ,(∀ i,∑ j : F.frozen,c j*(RingHom.id ℝ) (a j.val.succ i)=0)→∀ j,c j=0 :=by
    intro c HC
    apply IntegralMixedSelectedComponentSampling.normal_independent F.frozen q
      (fun i=>Int.cast_ne_zero.mpr (F.scales_ne_zero i)) h c
    simpa only [a,RingHom.id_apply] using HC
  have Hobj : ¬∃ c : F.frozen→ℝ,∀ i,(RingHom.id ℝ) (a 0 i)=
      ∑ j : F.frozen,c j*(RingHom.id ℝ) (a j.val.succ i) :=by
    simpa only [a,RingHom.id_apply] using
      IntegralMixedSelectedComponentSampling.objective_independent F.frozen q h hh
  obtain ⟨y,mu,HY,HR⟩:=FlatAffineSingularComponentSampling.exists_component_stage_root (RingHom.id ℝ)
    p F.frozen a b (fun i=>Fin.elim0 i) (HE.symm ▸ hc) Hind Hobj z
    (by rw [IntegralMixedSelectedComponentSampling.polynomial_eval];exact hz.1)
    (fun j hj=>by simpa [a,PhysicalPowerCriticalRows.coordinateNormals,q,H,b,eq_comm] using hz.2 j hj)
  rw [HE] at HY
  have HG:=(FlatAffineCriticalStage.roots_iff (RingHom.id ℝ) p F.frozen a b
    (Sum.elim (fun i : Fin 0=>Fin.elim0 i) (Sum.elim y mu))).mp HR
  refine ⟨y,HY,?_⟩
  intro i hi hih
  have HP:=HG.2.2.1 i
  have HU:=HG.2.2.2 i hi
  change mu i.succ=0 at HU
  change (pderiv i p).eval₂ (RingHom.id ℝ) y=∑ j,(RingHom.id ℝ) (a j i)*mu j at HP
  have HS:=PhysicalPowerCriticalRows.normal_power_sum (RingHom.id ℝ) 2 q h i mu 1
  simp only [RingHom.id_apply,pow_one,ite_eq_right hih,HU,mul_zero,zero_add] at HS
  have HZ : (pderiv i p).eval₂ (RingHom.id ℝ) y=0:=HP.trans (by simpa only [a,RingHom.id_apply] using HS)
  simpa only [p,IntegralMixedSelectedComponentSampling.polynomial,pderiv_map,eval₂_map,RingHom.id_comp] using HZ

/-- Properness of the actual source supplies compactness internally. -/
theorem exists_component_critical_of_proper (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen)
    (hp : IsProperMap (fun y : Fin (n+1)→ℝ=>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y))
    (z : Fin (n+1)→ℝ) (hz : z∈slice P F values) :
    ∃ y : Fin (n+1)→ℝ,y∈connectedComponentIn (slice P F values) z ∧
      ∀ i,i∉F.frozen→i≠h→
        (pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
          (Int.castRingHom ℝ) y=0 :=by
  apply exists_component_objective_critical P F values h hh ?_ z hz
  exact (hp.isCompact_preimage (isCompact_singleton : IsCompact ({0} : Set ℝ))).of_isClosed_subset
    (slice_closed P F values) (fun _ hy=>hy.1)

/-- The sample's height is an actual critical sweep value. -/
theorem exists_component_critical_height (P : SpatialSource n) (F : Frame n)
    (values : Fin k→ℝ) (h : Fin (n+1)) (hh : h∉F.frozen) (HF : FreeNormal F)
    (hc : IsCompact (slice P F values)) (z : Fin (n+1)→ℝ) (hz : z∈slice P F values) :
    ∃ y : Fin (n+1)→ℝ,y∈connectedComponentIn (slice P F values) z ∧
      y h∈realCriticalValues P (line F h) values h :=by
  obtain ⟨y,HY,HG⟩:=exists_component_objective_critical P F values h hh hc z hz
  exact ⟨y,HY,(line_realCriticalValues_iff P F values h hh HF _).mpr
    ⟨y,connectedComponentIn_subset _ _ HY,rfl,HG⟩⟩

/-- The actual bounded source supplies properness and compactness internally. -/
theorem regular_component_objective_critical (R : LeanCanny.Encoding.BoundedFullWriter.Readers)
    (q : List Bool) (F : Frame (R.dim q+3)) (values : Fin k→ℝ)
    (h : Fin (R.dim q+4)) (hh : h∉F.frozen)
    (z : Fin (R.dim q+4)→ℝ)
    (hz : z∈slice (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q) F values) :
    ∃ y : Fin (R.dim q+4)→ℝ,
      y∈connectedComponentIn (slice (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q) F values) z ∧
      ∀ i,i∉F.frozen→i≠h→
        (pderiv i (FermatCriticalHomogenization.polynomial
          (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q).low
          (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q).leading
          (LeanCanny.Encoding.BoundedRegularLowModularTerm.source R q).degree)).eval₂ (Int.castRingHom ℝ) y=0 :=
  exists_component_critical_of_proper _ F values h hh (regular_source_proper R q) z hz

end LeanCanny.Geometry.IntegralMixedFrozenFrame
