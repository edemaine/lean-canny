/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralRelativeJointRootGuard
public import LeanCanny.Algebra.IntegralMixedRelativeCutFiniteGuards
public import LeanCanny.Algebra.IntegralMixedCutMatrix
/-! # Finite selected-degree guards and the actual cut successor row

All four relative cut tags use the same parent hom and complete successor
tuple. Finite lower-choice and coefficient tests establish actual Kind
validity and the recorded degree. The remaining root test reduces exactly
to the newest retained quotient and the untruncated constant coefficient.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRelativeCuts
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem joint_coefficient_guards (x : State P S B m ι) (hm : m≤S) (r : Rule n) (c : Kind P r)
    (d : ℕ) (hdN : d≤2^B) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin (m+1)→ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z i.succ^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (hc : CoefficientGuards x hm r φ c d)
    (hz : ∀ i, (UniformIntegralPrefixRows.rows S x.sampler.scalarPrefix.rows x.sampler.scalarPrefix.basis
      (normalizedScalarPolynomial x (IntegralMixedCutMatrix.raw x hm r c d) d) d i).eval₂ (Int.castRingHom ℝ) z=0) :
    Valid x hm r φ c ∧ ((factor x hm r c).map φ.toRingHom).natDegree=d ∧
      ((factor x hm r c).eval₂ φ.toRingHom
        (IntegralRelativeTruncation.jointQuotient x.sampler.scalarPrefix (factor x hm r c) d z)=0 ↔
        IntegralRelativeTruncation.jointQuotient x.sampler.scalarPrefix (factor x hm r c) d z≠0 ∨
          φ.toRingHom ((factor x hm r c).coeff 0)=0) := by
  have hv:=coefficientGuards_valid x hm r φ c d hc
  have hd:=coefficientGuards_degree x hm r φ c d hc
  refine ⟨hv,hd,?_⟩
  have hp : (factor x hm r c).map φ.toRingHom≠0 :=
    (valid_iff_lower_factors x hm r φ c).mp hv |>.2
  exact IntegralRelativeTruncation.joint_root_guard x.sampler.scalarPrefix (factor x hm r c) d hdN φ z hφ hz hp hd

end LeanCanny.Algebra.IntegralMixedRelativeCuts
