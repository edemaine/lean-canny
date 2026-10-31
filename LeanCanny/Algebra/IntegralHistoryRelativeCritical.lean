/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryRelativeExtension

/-! # Actual critical history roots construct their next scalar equation

For a frozen initial coordinate block, the retained critical equations
imply the relative annihilator relations. The resulting scalar equation
is constructed from the actual source and retained height elements. Every
physical critical root extends to it without changing its full tuple.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m n k : ℕ} {ι : Type} [Fintype ι]

noncomputable def criticalCandidate (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n)
    (offset : ℕ) (hfit : offset + (k + 1) = n + 1) (r j : Fin (k + 1)) : Polynomial F.scalarPrefix.carrier :=
  CoordinateFrozenCriticalElimination.polynomial data.degree data.scales data.heights offset hfit
    (data.low.map (Int.castRingHom F.scalarPrefix.carrier)) (data.leading : F.scalarPrefix.carrier) r j

theorem criticalCandidate_root (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n)
    (offset : ℕ) (hfit : offset + (k + 1) = n + 1)
    (hfrozen : ∀ i, i ∈ data.frozen ↔ i.val < offset) (r j : Fin (k + 1))
    (hfree : data.free = ClearedCoordinateCritical.freeIndex offset hfit.le r)
    (z : (ι ⊕ Variables (n + 1)) → ℝ)
    (hz : ∀ l, ((criticalStep F data).rows l).eval₂ (Int.castRingHom ℝ) z = 0) :
    ∃ φ : F.scalarPrefix.carrier →ₐ[ℤ] ℝ,
      (∀ i, φ (F.scalarPrefix.basis.generator i) = z (Sum.inl (F.scalar i)) ^ weights S N m i) ∧
      ((criticalCandidate F data offset hfit r j).map φ.toRingHom).natDegree =
        PurePowerReductionBounds.dimension (k + 1) data.degree ∧
      (criticalCandidate F data offset hfit r j).eval₂ φ.toRingHom
        (z (ambient (ClearedCoordinateCritical.freeIndex offset hfit.le j)) ^ physical S N m) = 0 := by
  obtain ⟨φ, _hold, hφ, hsource, hheight, hgrad, hinactive⟩ := criticalStep_roots_interpret F data z hz
  let x := fun i => z (ambient i) ^ physical S N m
  let mu := fun l => z (multiplier l) ^ ((data.degree - 1) * physical S N m)
  have HC : φ.toRingHom.comp (Int.castRingHom F.scalarPrefix.carrier) = Int.castRingHom ℝ := Subsingleton.elim _ _
  have HP : FermatCriticalHomogenization.polynomial (data.low.map (Int.castRingHom F.scalarPrefix.carrier))
      (data.leading : F.scalarPrefix.carrier) data.degree =
      (FermatCriticalHomogenization.polynomial data.low data.leading data.degree).map (Int.castRingHom F.scalarPrefix.carrier) :=
    (FermatCriticalHomogenization.map_polynomial (Int.castRingHom F.scalarPrefix.carrier) data.low data.leading data.degree).symm
  have HA : φ (data.leading : F.scalarPrefix.carrier) ≠ 0 := by
    change φ.toRingHom (data.leading : F.scalarPrefix.carrier) ≠ 0
    rw [map_intCast]
    exact Int.cast_ne_zero.mpr data.leading_ne
  refine ⟨φ, hφ, ?_, ?_⟩
  · exact CoordinateFrozenCriticalElimination.specialized_degree φ.toRingHom data.degree (by have := data.degree_two; omega)
      data.scales data.scales_ne data.heights offset hfit _ _ HA r j
  · apply CoordinateFrozenCriticalElimination.root φ.toRingHom data.degree data.degree_two data.scales
      data.scales_ne data.heights offset hfit _ _
      ((PolynomialMapDegree.degree_le _ data.low).trans_lt data.low_degree) r x
    · intro i hi
      have HE := PhysicalPowerCriticalRows.normal_height_sum (Int.castRingHom ℝ) data.objective data.scales data.free i x 1
      simp only [pow_one] at HE
      exact HE.symm.trans (hheight i ((hfrozen i).mpr hi))
    · rw [HP, eval₂_map, HC]
      exact hsource
    · intro i hi
      rw [HP, pderiv_map, eval₂_map, HC]
      apply CoordinateFrozenCriticalElimination.free_gradient_zero (Int.castRingHom ℝ) _ data.objective
        data.scales data.frozen data.free x mu hgrad hinactive
      · intro Hmem
        have HH := (hfrozen _).mp Hmem
        dsimp only [ClearedCoordinateCritical.freeIndex] at HH
        omega
      · rw [hfree]
        intro HE
        apply hi
        apply Fin.ext
        have HV := congrArg Fin.val HE
        dsimp only [ClearedCoordinateCritical.freeIndex] at HV
        omega

theorem criticalCandidate_real_extend_recover (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n)
    (hN : 0 < N) (hcap : PurePowerReductionBounds.dimension (k + 1) data.degree ≤ N)
    (offset : ℕ) (hfit : offset + (k + 1) = n + 1)
    (hfrozen : ∀ i, i ∈ data.frozen ↔ i.val < offset) (r j : Fin (k + 1))
    (hfree : data.free = ClearedCoordinateCritical.freeIndex offset hfit.le r)
    (z : (ι ⊕ Variables (n + 1)) → ℝ)
    (hz : ∀ l, ((criticalStep F data).rows l).eval₂ (Int.castRingHom ℝ) z = 0) :
    let G := criticalStep F data
    let p := criticalCandidate F data offset hfit r j
    let d := PurePowerReductionBounds.dimension (k + 1) data.degree
    ∃ y : ((ι ⊕ Variables (n + 1)) ⊕ Unit) → ℝ,
      (∀ l, ((scalarStep G data.birth_bound hN p d).rows l).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (scalarStep G data.birth_bound hN p d).scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((scalarStep G data.birth_bound hN p d).scalarPrefix.basis.generator i) =
          y ((scalarStep G data.birth_bound hN p d).scalar i) ^ weights S N (m + 1) i) →
        ψ (PaddedIntegralParameterExtension.numerator F.scalarPrefix.basis p d) /
          ((PaddedIntegralParameterExtension.denominator F.scalarPrefix.basis p d : ℤ) : ℝ) =
          z (ambient (ClearedCoordinateCritical.freeIndex offset hfit.le j)) ^ physical S N m := by
  obtain ⟨φ, hφ, hd, hp⟩ := criticalCandidate_root F data offset hfit hfrozen r j hfree z hz
  exact scalarStep_real_extend_recover (criticalStep F data) data.birth_bound hN _ _ hcap z hz φ hφ _ hd
    (Nat.succ_le_of_lt (pow_pos (Nat.two_pow_pos _) _)) hp

end LeanCanny.Algebra.IntegralHistorySampler
