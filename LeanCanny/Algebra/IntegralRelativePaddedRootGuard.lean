/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PaddedIntegralRootGuard
public import LeanCanny.Algebra.IntegralRelativeTruncation
/-! # Exact root guards for integer-leading relative cut normalization

The old homomorphism is the same in the factor, truncation, inverse
normalization and padded equation. A padded root at a nonzero quotient is
an actual factor root. A zero quotient requires precisely the untruncated
factor's constant coefficient to vanish, including scalar degree zero.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeTruncation
open Polynomial
open scoped Classical
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

theorem padded_root_guard (b : Module.Basis ι ℤ A) (p : Polynomial A) (d N : ℕ)
    (φ : A→ₐ[ℤ]ℝ) (hp : p.map φ.toRingHom≠0) (hd : (p.map φ.toRingHom).natDegree=d)
    (hdN : d≤N) (a : ℝ)
    (hz : (PaddedIntegralNormalization.polynomial (normalized b p d) d N).eval₂ φ.toRingHom
      (φ ((normalized b p d).coeff d)*a)=0) :
    p.eval₂ φ.toRingHom a=0 ↔ a≠0 ∨ φ.toRingHom (p.coeff 0)=0 := by
  constructor
  · intro hroot
    by_cases ha : a=0
    · right
      simpa only [ha,eval₂_at_zero] using hroot
    · exact Or.inl ha
  · intro hg
    by_cases ha : a=0
    · have hc := hg.resolve_left (fun hne=>hne ha)
      simpa only [ha,eval₂_at_zero] using hc
    · have hlead : φ ((normalized b p d).coeff d)≠0 := by
        rw [normalized,IntegralRelativeLeadingNormalization.coefficient,map_intCast]
        exact Int.cast_ne_zero.mpr (IntegralRelativeLeadingNormalization.denominator_ne_zero b ((truncate p d).coeff d))
      have hnorm := PaddedIntegralNormalization.scaled_root_converse (normalized b p d) d N hdN φ.toRingHom
        (normalized_degree b p d φ) hlead a ha hz
      exact (root_iff b p d φ hd hp a).mp hnorm

end LeanCanny.Algebra.IntegralRelativeTruncation
