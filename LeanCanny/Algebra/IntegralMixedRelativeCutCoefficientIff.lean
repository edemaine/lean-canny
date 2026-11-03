/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutFiniteGuards
/-! # Exact semantic completeness of the finite cut coefficient guards -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem coefficientGuards_iff_valid_degree (x : State P S B m ι) (hm : m≤S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind P r) (d : ℕ) :
    CoefficientGuards x hm r φ c d ↔
      Valid x hm r φ c ∧ ((factor x hm r c).map φ.toRingHom).natDegree=d :=by
  constructor
  · intro h
    exact ⟨coefficientGuards_valid x hm r φ c d h,coefficientGuards_degree x hm r φ c d h⟩
  · rintro ⟨hv,hd⟩
    have HL:=(valid_iff_lower_factors x hm r φ c).mp hv
    refine ⟨?_,?_,?_⟩
    · intro k hk j _
      have H:=congrArg (fun p : Polynomial ℝ=>p.coeff j) (HL.1 k hk)
      simpa only [coeff_map,coeff_zero] using H
    · have H:=Polynomial.leadingCoeff_ne_zero.mpr HL.2
      rw [leadingCoeff,hd,coeff_map] at H
      exact H
    · intro j hj _
      have H:=Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hj)
      rw [coeff_map] at H
      exact H

end LeanCanny.Algebra.IntegralMixedRelativeCuts
