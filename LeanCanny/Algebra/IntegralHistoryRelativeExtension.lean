/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateFrozenCriticalElimination
public import LeanCanny.Algebra.IntegralHistoryRealExtension

/-! # Constructed relative critical candidates extend the complete history

The scalar polynomial is the actual frozen-slice annihilator, rather than
an input vanishing-polynomial certificate. Its advertised degree depends
only on free spatial arity and source degree. Every critical coordinate
extends the same full parent root and is recovered by the canonical height.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial CoordinateFrozenCriticalElimination UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m n k : ℕ} {ι : Type} [Fintype ι]

theorem relativeCritical_real_extend_recover (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (D : ℕ) (hD : 2 ≤ D) (hcap : PurePowerReductionBounds.dimension (k + 1) D ≤ N)
    (scales : Fin (n + 1) → ℤ) (hc : ∀ i, scales i ≠ 0)
    (H : Fin (n + 1) → F.scalarPrefix.carrier) (offset : ℕ) (hfit : offset + (k + 1) = n + 1)
    (low : MvPolynomial (Fin (n + 1)) F.scalarPrefix.carrier) (a : F.scalarPrefix.carrier)
    (hlow : low.totalDegree < D) (r j : Fin (k + 1))
    (z : ι → ℝ) (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : F.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (F.scalarPrefix.basis.generator i) = z (F.scalar i) ^ weights S N m i)
    (ha : φ a ≠ 0) (x : Fin (n + 1) → ℝ)
    (hfrozen : ∀ i, i.val < offset → (scales i : ℝ) * x i = φ (H i))
    (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ.toRingHom x = 0)
    (hg : ∀ i : Fin (k + 1), i ≠ r →
      (pderiv (ClearedCoordinateCritical.freeIndex offset hfit.le i)
        (FermatCriticalHomogenization.polynomial low a D)).eval₂ φ.toRingHom x = 0) :
    let p := CoordinateFrozenCriticalElimination.polynomial D scales H offset hfit low a r j
    let d := PurePowerReductionBounds.dimension (k + 1) D
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ l, ((scalarStep F hm hN p d).rows l).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (scalarStep F hm hN p d).scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((scalarStep F hm hN p d).scalarPrefix.basis.generator i) =
          y ((scalarStep F hm hN p d).scalar i) ^ weights S N (m + 1) i) →
        ψ (PaddedIntegralParameterExtension.numerator F.scalarPrefix.basis p d) /
          ((PaddedIntegralParameterExtension.denominator F.scalarPrefix.basis p d : ℤ) : ℝ) =
          x (ClearedCoordinateCritical.freeIndex offset hfit.le j) := by
  dsimp only
  apply scalarStep_real_extend_recover F hm hN _ _ hcap z hz φ hφ
    (x (ClearedCoordinateCritical.freeIndex offset hfit.le j))
  · exact CoordinateFrozenCriticalElimination.specialized_degree φ.toRingHom D (by omega)
      scales hc H offset hfit low a ha r j
  · exact Nat.succ_le_of_lt (pow_pos (Nat.two_pow_pos _) _)
  · exact CoordinateFrozenCriticalElimination.root φ.toRingHom D hD scales hc H offset hfit low a hlow r x hfrozen hp hg j

end LeanCanny.Algebra.IntegralHistorySampler
