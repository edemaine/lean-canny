/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHeightSyntax
public import LeanCanny.ETR.PolynomialMass

/-! # Original polynomial syntax supplies its own coefficient-height ceiling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOriginalSpatialHeight
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript

def height (t : List Bool → ETR.Term) (r : List Bool) : ℕ := (t r).toData.size + 1

theorem height_unary (t : List Bool → ETR.Term)
    (ht : (fun r => (t r).toData.toBits) ∈ FP) : UnaryFn (height t) :=
  ((UnaryFn.length ht).of_eq (fun r => Data.length_toBits (t r).toData)).add (UnaryFn.const 1)

theorem coefficient_bound (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (t : List Bool → ETR.Term)
    (hp : ∀ r, (t r).finitePolynomial (P.ambient r + 1) = (D.spatial r).low)
    (r : List Bool) (e : Fin (P.ambient r + 1) →₀ ℕ) :
    ((D.spatial r).low.coeff e).natAbs ≤ 2 ^ height t r := by
  rw [← hp r]
  exact (MvMass.coeff_le _ e).trans ((t r).finitePolynomial_mass _ |>.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ _)))

theorem inputs (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (t : List Bool → ETR.Term) (L : List Bool → ℕ)
    (hp : ∀ r, (t r).finitePolynomial (P.ambient r + 1) = (D.spatial r).low)
    (hl : ∀ r, (D.spatial r).leading.natAbs.size ≤ height t r)
    (hc : ∀ r, ∀ c ∈ D.rules r, IntegralMixedFullScriptHeight.CommandBounds (height t r) (L r) c)
    (hf : ∀ key, IntegralMixedFullHeightBits.RuleBounds (height t (pairFst key))
      (L (pairFst key)) (D.fallback key).rule) :
    IntegralMixedFullHeightBits.Inputs P D (height t) L :=
  IntegralMixedFullHeightBits.inputs_of_syntax P D (height t) L
    (coefficient_bound P D t hp) hl hc hf

end LeanCanny.Algebra.IntegralMixedOriginalSpatialHeight
