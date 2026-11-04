/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateLocalPath
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedSweepRetarget
public import LeanCanny.Geometry.IntegralMixedBankValueInterpretation
/-! # Anchored Near statements on literal equal prefix snapshots -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedSelectedNearTransport
open LeanCanny.Algebra LeanCanny.Connectivity IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private def BranchNearAt {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint t : ℝ) (j : ℕ) (mid child : ℝ) : Prop:=
  ∃hj : j<n-r.critical.offset.val+1,
    IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b endpoint ⟨j,hj⟩
      (IntegralMixedSelectedRootRank.rank x hm r φ t ⟨j,hj⟩ mid) child

private theorem branch_near_iff {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (a b endpoint t : ℝ)
    (j : Fin (n-r.critical.offset.val+1)) (mid child : ℝ) :
    BranchNearAt x hm r φ a b endpoint t j.val mid child↔
      IntegralMixedSelectedCoordinateEndpoint.Near x hm r φ a b endpoint j
        (IntegralMixedSelectedRootRank.rank x hm r φ t j mid) child :=by
  constructor
  · rintro ⟨hj,H⟩
    exact H
  · exact fun H=>⟨j.isLt,H⟩

theorem anchored_near_iff_of_snapshot (A B : IntegralMixedPrefixSnapshot.Data) (he : A=B)
    (hc : Canonical A.state) (hm : A.birth≤A.horizon) (hl : B.birth≤B.horizon)
    (r : Rule A.ambient) (s : Rule B.ambient)
    (hs : HEq (IntegralMixedSweepRetarget.rule r 0) (IntegralMixedSweepRetarget.rule s 0))
    (φ : A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : B.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (H : ∀(i : Fin A.birth) (j : Fin B.birth),i.val=j.val→
      φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=
      ψ (B.state.bank.numerator j)/(B.state.bank.denominator j:ℝ))
    (j : Fin (A.ambient-r.critical.offset.val+1))
    (k : Fin (B.ambient-s.critical.offset.val+1)) (hj : j.val=k.val)
    (a b endpoint t mid child : ℝ) :
    IntegralMixedSelectedCoordinateEndpoint.Near A.state hm r φ a b endpoint j
      (IntegralMixedSelectedRootRank.rank A.state hm r φ t j mid) child ↔
    IntegralMixedSelectedCoordinateEndpoint.Near B.state hl s ψ a b endpoint k
      (IntegralMixedSelectedRootRank.rank B.state hl s ψ t k mid) child :=by
  cases he
  have HP : φ=ψ:=IntegralMixedBankValueInterpretation.hom_ext A.state hc φ ψ
    (fun i=>H i i rfl)
  subst ψ
  have HS : IntegralMixedSweepRetarget.rule r 0=IntegralMixedSweepRetarget.rule s 0:=eq_of_heq hs
  rw [←branch_near_iff A.state hm r φ a b endpoint t j mid child,
    ←branch_near_iff A.state hl s φ a b endpoint t k mid child]
  change BranchNearAt A.state hm (IntegralMixedSweepRetarget.rule r 0) φ a b endpoint t j.val mid child↔
    BranchNearAt A.state hl (IntegralMixedSweepRetarget.rule s 0) φ a b endpoint t k.val mid child
  rw [HS,hj]

end LeanCanny.Geometry.IntegralMixedSelectedNearTransport
