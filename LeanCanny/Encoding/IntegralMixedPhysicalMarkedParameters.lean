/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedOldInterpretation
public import LeanCanny.Geometry.BoundedMarkedParameterSemantics
/-! # Original marked leaf roots determine the intended real parameters -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original oldKey tail beta)
open IntegralMixedAuxiliaryParametricSlackSource (regularizationAt penaltyAt)
open IntegralMixedAuxiliaryMarkedOldInterpretation (count_at charge_at)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  (R : List Bool→ℕ) (outer : Bool) (ctx : List Bool) (v : ℕ→ℝ)
  (h : ∀i<number n ctx+(if outer then 10 else 8),((originalSource hn ht ha (R:=R) outer).polynomial
    (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0)

include h in
theorem marked_roots : ∀i<number n ctx+8,((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial
    (pair ctx (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0 :=by
  cases outer
  · exact h
  · exact IntegralFramedPhysicalLeafSources.outer_marked_roots hn ht ha R ctx v h

include h in
theorem parameters :
    v (number n ctx+4)=(2:ℝ)^R ctx ∧
    v (number n ctx+5)=(2:ℝ)^LeanCanny.Geometry.BoundedRegularSource.regularizationExponent
      (number n ctx) (t (original ctx)).toData.size (t (original ctx)).toData.size (R ctx) ∧
    v (number n ctx+6)=(2:ℝ)^LeanCanny.Geometry.BoundedZeroSource.perturbationExponent
      (number n ctx) (t (original ctx)).toData.size (t (original ctx)).toData.size (R ctx) ∧
    v (number n ctx+7)=(2:ℝ)^LeanCanny.Geometry.BoundedZeroSource.penaltyExponent
      (number n ctx) (t (original ctx)).toData.size (R ctx) :=by
  have HM:=marked_roots hn ht ha R outer ctx v h
  have HR : (R∘tail) (oldKey n t ctx)=R ctx:=congrArg R (IntegralMixedAuxiliaryMarkedIntegerSource.oldKey_tail n t ctx)
  obtain ⟨E5,E6,E7⟩:=IntegralFramedPhysicalLeafSources.parameters hn ht ha R ctx v HM
  refine ⟨IntegralFramedPhysicalLeafSources.radius hn ht ha R ctx v HM,?_,?_,?_⟩
  · simpa only [regularizationAt,count_at,charge_at,HR,LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance] using E5
  · simpa only [beta,count_at,charge_at,HR,LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance] using E6
  · simpa only [penaltyAt,count_at,charge_at,HR,LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance] using E7
end LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
