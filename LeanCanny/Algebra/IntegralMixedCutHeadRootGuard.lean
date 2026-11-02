/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutJointRootGuard
/-! # Native head-zero testing removes exactly the scalar padding roots

The actual quotient is zero exactly when the newest joint root coordinate
is zero. Its integer denominator may be negative or a nonunit modulo the
query modulus; neither sign nor modular inversion is needed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeTruncation
open scoped Classical
variable {S B m : ℕ}

theorem jointQuotient_zero_iff (P : UniformIntegralPrefix.Prefix S (2^B) m)
    (p : Polynomial P.carrier) (d : ℕ) (z : Fin (m+1)→ℝ) :
    jointQuotient P p d z=0 ↔ z 0=0 := by
  have HD : (IntegralRelativeLeadingNormalization.denominator P.basis.finBasis ((truncate p d).coeff d) : ℝ)≠0 :=
    Int.cast_ne_zero.mpr (IntegralRelativeLeadingNormalization.denominator_ne_zero _ _)
  rw [jointQuotient,div_eq_zero_iff]
  simp only [HD,or_false]
  exact pow_eq_zero_iff (UniformIntegralPowerSchedule.birth_pos S (2^B) m).ne'

end LeanCanny.Algebra.IntegralRelativeTruncation

namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem head_root_guard (x : State P S B m ι) (hm : m≤S) (r : Rule n) (c : Kind P r)
    (d : ℕ) (hdN : d≤2^B) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin (m+1)→ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z i.succ^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (hc : CoefficientGuards x hm r φ c d)
    (hz : ∀ i, (UniformIntegralPrefixRows.rows S x.sampler.scalarPrefix.rows x.sampler.scalarPrefix.basis
      (normalizedScalarPolynomial x (IntegralMixedCutMatrix.raw x hm r c d) d) d i).eval₂ (Int.castRingHom ℝ) z=0) :
    (factor x hm r c).eval₂ φ.toRingHom
      (IntegralRelativeTruncation.jointQuotient x.sampler.scalarPrefix (factor x hm r c) d z)=0 ↔
      z 0≠0 ∨ φ.toRingHom ((factor x hm r c).coeff 0)=0 := by
  have HR:=(joint_coefficient_guards x hm r c d hdN φ z hφ hc hz).2.2
  exact HR.trans (or_congr
    (not_congr (IntegralRelativeTruncation.jointQuotient_zero_iff x.sampler.scalarPrefix (factor x hm r c) d z)) Iff.rfl)

end LeanCanny.Algebra.IntegralMixedRelativeCuts
