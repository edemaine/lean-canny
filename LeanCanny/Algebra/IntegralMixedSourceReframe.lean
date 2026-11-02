/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistorySemantics
/-! # Explicit changes of spatial source over an unchanged retained prefix

A source change is a new continuation state, not a reinterpretation of the old
commands under the new source. The sampler, every physical row, coefficient
algebra, integer denominator and interpreting hom remain literally unchanged.
A source-dependent critical dimension cap is the only new state obligation.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
variable {n n' S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def reframe (x : State P S B m ι) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree ≤ 2^B) : State Q S B m ι where
  sampler := x.sampler
  bank := x.bank
  denominator_ne_zero := x.denominator_ne_zero
  critical_cap := hcap

theorem reframe_sampler (x : State P S B m ι) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree ≤ 2^B) :
    (reframe x Q hcap).sampler=x.sampler := rfl

theorem reframe_bank (x : State P S B m ι) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree ≤ 2^B) :
    (reframe x Q hcap).bank=x.bank := rfl

theorem reframe_denominator (x : State P S B m ι) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree ≤ 2^B) :
    commonDenominator (reframe x Q hcap)=commonDenominator x := rfl

theorem reframe_expression (x : State P S B m ι) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree ≤ 2^B) (a : AffineExpr) :
    expression (reframe x Q hcap) a=expression x a := by
  induction a with
  | constant c => rfl
  | reference j => rfl
  | add a b ha hb =>
    simp only [expression,ha,hb]
    rfl
  | scale c a ha =>
    simp only [expression,ha]
    rfl

theorem reframe_same (x : State P S B m ι) : reframe x P x.critical_cap=x := by
  cases x
  rfl

noncomputable def reframeDegree (x : State P S B m ι) (Q : SpatialSource n)
    (hdegree : Q.degree=P.degree) : State Q S B m ι :=
  reframe x Q (by rw [hdegree]; exact x.critical_cap)

theorem reframe_recover (x : State P S B m ι) (Q : SpatialSource n')
    (hcap : PurePowerReductionBounds.dimension (n'+1) Q.degree ≤ 2^B)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i) :
    ∀ i, φ ((reframe x Q hcap).bank.numerator i)/
      ((reframe x Q hcap).bank.denominator i:ℝ)=values i := H

end LeanCanny.Algebra.IntegralMixedHistory
