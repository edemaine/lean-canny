/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.UniformIntegralPrefixJointRoots
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
public import LeanCanny.Algebra.IntegralMixedHistorySemantics

/-! # A joint natural-coordinate tuple constructs actual cleared bank values -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedObservedInterpretation
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem exists_interpretation (x : State P S B m ι) (H : Canonical x) (z : ℕ→ℝ)
    (hz : UniformIntegralPrefix.RootsAt x.sampler.scalarPrefix z) :
    ∃ φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i,φ (cleared x i)=(commonDenominator x : ℝ)*(IntegralMixedFramedBankObservation.ofState x).point z i.val := by
  obtain ⟨φ,hφ⟩:=x.sampler.scalarPrefix.interpret ℝ (fun j=>z j.val) hz
  have HV:=IntegralMixedCanonicalBankPoint.quotient_eq x H (fun j=>z j.val) φ hφ
  refine ⟨φ,fun i=>?_⟩
  have HP : IntegralMixedCanonicalBankPoint.point x (fun j=>z j.val) i=
      (IntegralMixedFramedBankObservation.ofState x).point z i.val := by
    simp only [IntegralMixedFramedBankObservation.Data.point,IntegralMixedFramedBankObservation.ofState,dite_eq_left i.isLt]
    rfl
  exact (cleared_recover x φ (IntegralMixedCanonicalBankPoint.point x (fun j=>z j.val)) HV i).trans
    (congrArg (fun r : ℝ=>(commonDenominator x : ℝ)*r) HP)

end LeanCanny.Geometry.IntegralMixedObservedInterpretation
