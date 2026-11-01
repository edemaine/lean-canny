/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedSweepBounds
public import LeanCanny.Algebra.IntegralMixedNormalizedScalar
public import LeanCanny.Algebra.IntegralRelativeTruncation

/-! # Actual scalar-only births for every selected trailing cut

A root of the selected relative factor is retained over the CURRENT old
embedding. The actual specialized degree is bounded by the original
spatial ceiling. Branch-exact truncation and integer-leading normalization
preserve that root, including extraneous factor roots, with no physical
critical sample and no absolute norm-degree feedback.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedTrailingBirth
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedCoordinateTrailing UniformIntegralPowerSchedule Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def cutStep (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (ChoiceBound P r)) (d : ℕ) :
    State P S B (m + 1) (ι ⊕ Unit) :=
  normalizedScalarStep x hm (IntegralRelativeTruncation.truncate (factor x hm r j i) d) d

theorem cut_real_extend (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (ChoiceBound P r))
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (hi : Valid x hm r j φ i)
    (hcap : IntegralMixedSweepBounds.parameterCap (n + 1) P.degree ≤ 2 ^ B)
    (z : ι → ℝ) (hz : ∀ k, (x.sampler.rows k).eval₂ (Int.castRingHom ℝ) z = 0)
    (hφ : ∀ k, φ (x.sampler.scalarPrefix.basis.generator k) = z (x.sampler.scalar k) ^ weights S (2 ^ B) m k)
    (t : ℝ) (ht : (factor x hm r j i).eval₂ φ.toRingHom t = 0) :
    ∃ d ≤ IntegralMixedSweepBounds.parameterCap (n + 1) P.degree,
      ∃ y : (ι ⊕ Unit) → ℝ,
        (∀ k, ((cutStep x hm r j i d).sampler.rows k).eval₂ (Int.castRingHom ℝ) y = 0) ∧
        (∀ k, y (Sum.inl k) = z k) ∧
        ∀ ψ : (cutStep x hm r j i d).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
          (∀ k, ψ ((cutStep x hm r j i d).sampler.scalarPrefix.basis.generator k) =
            y ((cutStep x hm r j i d).sampler.scalar k) ^ weights S (2 ^ B) (m + 1) k) →
          ψ ((cutStep x hm r j i d).bank.numerator 0) /
            ((cutStep x hm r j i d).bank.denominator 0 : ℝ) = t := by
  let p := factor x hm r j i
  let d := (p.map φ.toRingHom).natDegree
  have HP : p.map φ.toRingHom ≠ 0 := factor_nonzero x hm r j φ i hi
  have HD : d ≤ IntegralMixedSweepBounds.parameterCap (n + 1) P.degree :=
    Polynomial.natDegree_map_le.trans (IntegralMixedSweepBounds.factor_degree x hm r j i)
  have Hroot : (p.map φ.toRingHom).eval₂ (RingHom.id ℝ) t = 0 := by
    rw [Polynomial.eval₂_id, Polynomial.eval_map]
    exact ht
  have Hpos : 1 ≤ d := Polynomial.natDegree_pos_of_eval₂_root HP (RingHom.id ℝ) Hroot (fun _ H => H)
  have HA : φ ((IntegralRelativeTruncation.truncate p d).coeff d) ≠ 0 := by
    rw [IntegralRelativeTruncation.coefficient, ite_eq_left (Nat.le_refl d)]
    have H := Polynomial.leadingCoeff_ne_zero.mpr HP
    rw [Polynomial.leadingCoeff, Polynomial.coeff_map] at H
    exact H
  have HT : (IntegralRelativeTruncation.truncate p d).eval₂ φ.toRingHom t = 0 :=
    (IntegralRelativeTruncation.eval_eq p d φ (Nat.le_refl d) t).trans ht
  exact ⟨d, HD, normalizedScalar_real_extend x hm (IntegralRelativeTruncation.truncate p d) d
    (IntegralRelativeTruncation.natDegree_le p d) Hpos (HD.trans hcap) z hz φ hφ HA t HT⟩

end LeanCanny.Algebra.IntegralMixedTrailingBirth
