/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedCutRecordBounds
public import LeanCanny.Encoding.IntegralMixedChosenLocalRealization
/-! # Actual selected cut choices and degrees fit the original record cap -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCutRecordConstructor
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
open IntegralMixedExceptionalBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem choice_le {n : ℕ} (P : SpatialSource n) (r : Rule n) (c : Kind P r) :
    IntegralMixedSweepRetarget.choiceIndex r c≤auxiliaryCap (n+1) P.degree :=by
  cases c with
  | coordinate j c=>
    have HC:=c.isLt
    have HB:=coordinateCap_le P.degree r
    change c.val<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree+1 at HC
    change c.val≤_
    unfold auxiliaryCap
    omega
  | squarefree j c=>
    have HC:=c.isLt
    have HB:=coordinateCap_le P.degree r
    change c.val<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree at HC
    change c.val≤_
    unfold auxiliaryCap
    omega
  | value j c=>
    have HC:=c.isLt
    have HB:=value_dimension_le P r
    have HD:=P.degree_two
    have HV : valueDimension (n+1) P.degree≤valueCap (n+1) P.degree:=by
      unfold valueCap
      exact Nat.le_mul_of_pos_right _ (by omega)
    change c.val<IntegralMixedGridValue.dimension P r+2 at HC
    change c.val≤_
    unfold auxiliaryCap
    omega
  | limitCoordinate j c=>
    have HC:=c.isLt
    have HB:=coordinateCap_le P.degree r
    change c.val<PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree+1 at HC
    change c.val≤_
    unfold auxiliaryCap
    omega

theorem Data.chosenCode_length {n birth B : ℕ} (d : Data n birth) (P : SpatialSource n) (Q : ℤ) (hQ : Q≠0)
    (c : Kind P (d.rule Q hQ)) (degree : ℕ)
    (hd : degree≤auxiliaryCap (n+1) P.degree) (hcap : auxiliaryCap (n+1) P.degree≤2^B) :
    (d.chosenCode Q hQ c degree).length≤codeBudget n birth B :=by
  unfold Data.chosenCode
  exact Data.code_length _ _ _ _ ((choice_le P _ c).trans hcap) (hd.trans hcap)

theorem critical_codeBudget_le (n birth B : ℕ) :
    IntegralMixedCriticalRecordConstructor.codeBudget n birth≤codeBudget n birth B :=by
  unfold IntegralMixedCriticalRecordConstructor.codeBudget codeBudget fieldBudget
  omega

end LeanCanny.Encoding.IntegralMixedCutRecordConstructor

namespace LeanCanny.Encoding.IntegralMixedChosenLocalRealization
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

omit [Fintype ι] in
theorem CutChoice.code_length (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (w : CutChoice x hm φ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (w.code x hm φ).length≤IntegralMixedCutRecordConstructor.codeBudget n m B :=by
  unfold CutChoice.code
  exact w.record.chosenCode_length P (commonDenominator x) (commonDenominator_ne_zero x) _ _
    (IntegralMixedRelativeCuts.selectedDegree_bound x hm _ φ _) hcap

omit [Fintype ι] in
theorem Choice.code_length (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (w : Choice x hm φ)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B) :
    (w.code x hm φ).length≤IntegralMixedCutRecordConstructor.codeBudget n m B :=by
  cases w with
  | inl w=>exact w.record.code_length.trans (IntegralMixedCutRecordConstructor.critical_codeBudget_le n m B)
  | inr w=>exact CutChoice.code_length x hm φ w hcap

omit [Fintype ι] in
theorem CutChoice.ofRule_value (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (d : IntegralMixedCutRecordConstructor.Data n m) (r : IntegralMixedCriticalSweep.Rule n)
    (hr : d.rule (commonDenominator x) (commonDenominator_ne_zero x)=r)
    (c : IntegralMixedRelativeCuts.Kind P r) (hc : IntegralMixedRelativeCuts.Valid x hm r φ c)
    (a : ℝ) (ha : (IntegralMixedRelativeCuts.factor x hm r c).eval₂ φ.toRingHom a=0) :
    (CutChoice.ofRule x hm φ d r hr c hc a ha).value=a :=by
  subst r
  rfl

end LeanCanny.Encoding.IntegralMixedChosenLocalRealization
