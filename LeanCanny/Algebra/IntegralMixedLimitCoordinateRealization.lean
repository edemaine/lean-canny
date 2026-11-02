/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRoot
public import LeanCanny.Algebra.IntegralMixedNormalizedScalar
public import LeanCanny.Algebra.IntegralRelativeTruncation

/-! # Correlated scalar realization of selected original limit coordinates

The storage degree is selected after the old hom. Truncating before inverse
normalization removes higher coefficients on that selected component. The
resulting actual scalar step retains every old physical coordinate and recovers
the original limit value. Only the original spatial scalar cap is used.

This module is independent of RelativeCuts and history tags.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinate
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open UniformIntegralPowerSchedule
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem degree_cap (x : State P S B m ι) (r : Rule n) : degree P r ≤ 2^B :=
  (IntegralCriticalFactorCeiling.dimension_mono (Nat.add_le_add_right (Nat.sub_le _ _) 1)
    (Nat.le_refl P.degree)).trans x.critical_cap

theorem factor_degree_bound (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) :
    (factor x hm r j c).natDegree ≤ degree P r :=
  (factor_degree x hm r j c).trans (Nat.le_of_lt_succ (show c.val<degree P r+1 from c.isLt))

theorem finite_roots (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c) :
    {a : ℝ | (factor x hm r j c).eval₂ φ.toRingHom a=0}.Finite := by
  simpa only [IsRoot,eval_map] using finite_setOfPred_isRoot hc.2

variable [Fintype ι]

noncomputable def step (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) (d : ℕ) :
    State P S B (m+1) (ι ⊕ Unit) :=
  normalizedScalarStep x hm (IntegralRelativeTruncation.truncate (factor x hm r j c) d) d

theorem real_extend (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c)
    (z : ι → ℝ) (hz : ∀ i, (x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (hφ : ∀ i, φ (x.sampler.scalarPrefix.basis.generator i)=
      z (x.sampler.scalar i)^weights S (2^B) m i)
    (a : ℝ) (ha : (factor x hm r j c).eval₂ φ.toRingHom a=0) :
    ∃ d ≤ degree P r, ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ i, ((step x hm r j c d).sampler.rows i).eval₂ (Int.castRingHom ℝ) y=0) ∧
      (∀ i, y (Sum.inl i)=z i) ∧
      ∀ ψ : (step x hm r j c d).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((step x hm r j c d).sampler.scalarPrefix.basis.generator i)=
          y ((step x hm r j c d).sampler.scalar i)^weights S (2^B) (m+1) i) →
        ψ ((step x hm r j c d).bank.numerator 0) / ((step x hm r j c d).bank.denominator 0:ℝ)=a := by
  let p := factor x hm r j c
  let d := (p.map φ.toRingHom).natDegree
  have HP : p.map φ.toRingHom≠0 := hc.2
  have HD : d ≤ degree P r := natDegree_map_le.trans (factor_degree_bound x hm r j c)
  have HRoot : (p.map φ.toRingHom).eval₂ (RingHom.id ℝ) a=0 := by
    rw [eval₂_id,eval_map]
    exact ha
  have HPos : 1 ≤ d := natDegree_pos_of_eval₂_root HP (RingHom.id ℝ) HRoot (fun _ H => H)
  have HA : φ ((IntegralRelativeTruncation.truncate p d).coeff d)≠0 := by
    rw [IntegralRelativeTruncation.coefficient,ite_eq_left (Nat.le_refl d)]
    have H := leadingCoeff_ne_zero.mpr HP
    rw [leadingCoeff,coeff_map] at H
    simpa only [d,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using H
  have HT : (IntegralRelativeTruncation.truncate p d).eval₂ φ.toRingHom a=0 :=
    (IntegralRelativeTruncation.eval_eq p d φ (Nat.le_refl d) a).trans ha
  exact ⟨d,HD,normalizedScalar_real_extend x hm (IntegralRelativeTruncation.truncate p d) d
    (IntegralRelativeTruncation.natDegree_le p d) HPos (HD.trans (degree_cap x r)) z hz φ hφ HA a HT⟩

end LeanCanny.Algebra.IntegralMixedLimitCoordinate
