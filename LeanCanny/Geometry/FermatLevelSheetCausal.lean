/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FermatLevelSheetProjection
public import LeanCanny.Geometry.IntegralMixedCausalLevelRegularity

/-! # The exact bounded level sheet for the actual causal Fermat source

For even degree its projected value interval is [-A-1,A-1]. The symmetric
capacity region [-A+1,A-1] is a subset. The causal exponent proves A>d, so
there is no supplied monotonicity or inverse-continuity premise.
-/
@[expose] public section
namespace LeanCanny.Geometry.FermatLevelSheet
open LeanCanny.Algebra IntegralMixedCausalLevelCapacity Set
open scoped Topology

theorem boundedForward_range (d : ℕ) (A : ℤ) (hd : Even d) (hA : (d:ℝ)<(A:ℝ)) :
    range (boundedForward d A)=Icc (-(A:ℝ)-1) ((A:ℝ)-1) := by
  have HE : range (boundedForward d A)=forward d A '' Icc (-1:ℝ) 1 := by
    ext w
    constructor
    · rintro ⟨v,rfl⟩
      exact ⟨v.val,v.property,rfl⟩
    · rintro ⟨v,hv,hw⟩
      exact ⟨⟨v,hv⟩,hw⟩
  rw [HE]
  have HC : Continuous (forward d A) := by unfold forward; fun_prop
  rw [HC.continuousOn.image_Icc_of_monotoneOn (by norm_num : (-1:ℝ)≤1)
    (strictMonoOn_forward d A hA).monotoneOn]
  simp only [forward,hd.neg_one_pow,mul_neg_one,one_pow,mul_one]

variable {n : ℕ}

noncomputable def causalHomeomorph (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D) :
    region (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G) ≃ₜ
      sheet (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G) :=
  projectionHomeomorph _ _ rfl (coefficient_gt_degree n D R G)

theorem causal_region_iff (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (x : Fin (n+1) → ℝ) :
    x∈region (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G) ↔
      (FermatLevelLift.polynomial (FixedLeadingTiltedSource.source k D u t ht)).eval₂ (Int.castRingHom ℝ) x∈
        Icc (-(coefficient n D R G:ℝ)-1) ((coefficient n D R G:ℝ)-1) := by
  change _∈range (boundedForward (FixedLeadingTiltedSource.degree D) (coefficient n D R G)) ↔ _
  rw [boundedForward_range _ _ (⟨2*D+1,by unfold FixedLeadingTiltedSource.degree; omega⟩ : Even (FixedLeadingTiltedSource.degree D))
    (coefficient_gt_degree n D R G)]

theorem causal_capacity_subset (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D) :
    {x | |(FermatLevelLift.polynomial (FixedLeadingTiltedSource.source k D u t ht)).eval₂ (Int.castRingHom ℝ) x|≤
      (coefficient n D R G:ℝ)-1}⊆region (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G) :=
  capacity_subset_region _ _ (⟨2*D+1,by change 4*D+2=(2*D+1)+(2*D+1); omega⟩)

theorem causal_lift_old (k D R G : ℕ) (u : Fin n) (t : ETR.Term) (ht : t.degreeBound≤D)
    (x : region (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D R G)) (i : Fin (n+1)) :
    (causalHomeomorph k D R G u t ht x).val i.castSucc=x.val i := by
  simp only [causalHomeomorph,projectionHomeomorph,Homeomorph.homeomorph_mk_coe,Equiv.coe_fn_mk,lift,Fin.snoc_castSucc]

end LeanCanny.Geometry.FermatLevelSheet
