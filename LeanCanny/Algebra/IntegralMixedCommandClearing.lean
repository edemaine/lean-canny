/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryScript
public import LeanCanny.Geometry.IntegralMixedFrozenFrame
/-! # Actual command clearing changes by its creating leading integer

The common denominator is not held fixed. At an interpreting hom retaining
the old quotient values, every shifted expression changes by that same
nonzero integer factor. No residue, leading-cost or matrix oracle is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHistory
open IntegralMixedFullHistoryScript
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem command_commonDenominator (x : State P S B m ι) (hm : m≤S) (c : Command P B) :
    commonDenominator (step x hm c)=leading x hm c*commonDenominator x :=by
  change (∏ i : Fin (m+1),(step x hm c).bank.denominator i)=
    leading x hm c*(∏ i : Fin m,x.bank.denominator i)
  rw [Fin.prod_univ_succ,step_denominator_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact step_denominator_succ x hm c i

theorem command_expression_later (x : State P S B m ι) (hm : m≤S) (c : Command P B)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)
    (e : AffineExpr) :
    ψ (expression (step x hm c) (LeanCanny.Geometry.IntegralMixedFrozenFrame.later e))=
      (leading x hm c:ℝ)*φ (expression x e) :=by
  rw [expression_recover (step x hm c) ψ _ HN,
    LeanCanny.Geometry.IntegralMixedFrozenFrame.evaluate_later,command_commonDenominator,
    Int.cast_mul,expression_recover x φ values H]
  ring

end LeanCanny.Algebra.IntegralMixedHistory
