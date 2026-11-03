/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotBad
public import LeanCanny.Algebra.IntegralMixedSelectedBadRetarget
/-! # Retargeted selected factors describe the same numerical parent bad set -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open IntegralMixedHistory IntegralMixedRelativeCuts
open LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem Data.mem_bad_retarget_factor_iff (d : Data) (labels : List Bool) (values : ℕ→ℝ)
    (hr : d.Ready labels) (hx : Canonical d.state)
    (φ : d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val)
    (j : ℕ) (a : ℝ) :
    a∈d.bad labels values ↔ ∃k : Kind d.source (IntegralMixedSweepRetarget.rule (d.rule labels hr) j),
      Valid d.state hr.1 (IntegralMixedSweepRetarget.rule (d.rule labels hr) j) φ k ∧
      IntegralMixedSelectedBadMembership.Ordinary (IntegralMixedSweepRetarget.rule (d.rule labels hr) j) k ∧
      (factor d.state hr.1 (IntegralMixedSweepRetarget.rule (d.rule labels hr) j) k).eval₂ φ.toRingHom a=0:=by
 obtain ⟨c⟩:=exists_choices d.state hr.1 (d.rule labels hr) φ
 let e:=IntegralMixedSweepRetarget.choices d.state hr.1 (d.rule labels hr) j φ c
 exact (d.mem_bad_iff labels values hr hx φ hφ c a).trans
   ((IntegralMixedSweepRetarget.bad_iff d.state hr.1 (d.rule labels hr) j φ c e a).symm.trans
     (IntegralMixedSelectedBadMembership.mem_bad_iff d.state hr.1 _ φ e a))

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
