/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHistory
/-! # Original spatial scales and the common bank denominator in a cleared height -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightCofactor
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def original (r : CriticalRule n) (i : Fin (n + 1)) : ℤ :=
  ∏ j ∈ Finset.univ.erase i, r.scales j

noncomputable def value (x : State P S B m ι) (r : CriticalRule n) (i : Fin (n + 1)) : ℤ :=
  commonDenominator x ^ n * original r i

theorem erased_scales (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (i : Fin (n + 1)) :
    CommonIntegerDenominator.denominator (Finset.univ.erase i) (data x hm r).scales =
      value x r i := by
  unfold CommonIntegerDenominator.denominator value original
  change (∏ j ∈ Finset.univ.erase i, commonDenominator x * r.scales j) = _
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]

theorem height (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n)
    (i : Fin (n + 1)) :
    CoordinateFrozenCriticalElimination.numerators (data x hm r).scales (data x hm r).heights i.val =
      (value x r i : x.sampler.scalarPrefix.carrier) * expression x (r.heights i) := by
  let _ := x.sampler.scalarPrefix.ring
  rw [CoordinateFrozenCriticalElimination.numerators, dite_eq_left i.isLt]
  change expression x (r.heights i) *
    (CommonIntegerDenominator.denominator (Finset.univ.erase i) (data x hm r).scales : _) = _
  rw [erased_scales, mul_comm]

end LeanCanny.Algebra.IntegralMixedHeightCofactor
