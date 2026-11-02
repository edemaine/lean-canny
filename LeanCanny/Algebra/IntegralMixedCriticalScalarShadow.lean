/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeScalar

/-! # A scalar-only critical shadow has the literal native prefix and bank

The physical samplers differ: a shadow adjoins no physical critical rows.
Only the coefficient prefix and retained bank are identified here.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem relativeScalar_prefix_eq_critical (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) :
    (relativeScalarStep x hm r).sampler.scalarPrefix=(criticalStep x hm r).sampler.scalarPrefix := rfl

theorem relativeScalar_bank_eq_critical (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) :
    (relativeScalarStep x hm r).bank=(criticalStep x hm r).bank := rfl

theorem relativeScalar_denominator_eq_critical (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) :
    commonDenominator (relativeScalarStep x hm r)=commonDenominator (criticalStep x hm r) := rfl

theorem relativeScalar_expression_eq_critical (x : State P S B m ι) (hm : m≤S) (r : CriticalRule n) (a : AffineExpr) :
    expression (relativeScalarStep x hm r) a=expression (criticalStep x hm r) a := by
  induction a with
  | constant c=>rfl
  | reference j=>rfl
  | add a b ha hb=>exact congrArg₂ (·+·) ha hb
  | scale c a ha=>exact congrArg ((c : (relativeScalarStep x hm r).sampler.scalarPrefix.carrier)*·) ha

end LeanCanny.Algebra.IntegralMixedHistory
