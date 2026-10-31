/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryCriticalStep
public import LeanCanny.Algebra.IntegralCoordinateEvaluation

/-! # Actual heights and critical equations on retained history roots

The scalar slots determine a unique algebra evaluation. The new physical
block uses those actual heights, while all earlier physical coordinates
remain in the parent root. Derivatives refer to the original source before
power substitution, including at singular critical roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {S N m n : ℕ} {ι K : Type} [CommRing K]

theorem interpret_unique (F : Sampler S N m ι) (z : ι → K)
    (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom K) z = 0) :
    ∃! φ : F.scalarPrefix.carrier →ₐ[ℤ] K,
      ∀ i, φ (F.scalarPrefix.basis.generator i) = z (F.scalar i) ^ weights S N m i := by
  obtain ⟨φ, hφ⟩ := F.interpret K z hz
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  exact F.scalarPrefix.basis.algHom_ext ψ φ (fun i => (hψ i).trans (hφ i).symm)

theorem historyHeights_eval (F : Sampler S N m ι) (H : Fin (n + 1) → F.scalarPrefix.carrier)
    (φ : F.scalarPrefix.carrier →ₐ[ℤ] K) (z : ι → K)
    (hφ : ∀ i, φ (F.scalarPrefix.basis.generator i) = z (F.scalar i) ^ weights S N m i) (i : Fin (n + 1)) :
    (historyHeights F H i).eval₂ (Int.castRingHom K) z = φ (H i) := by
  rw [historyHeights, eval₂_rename, CoordinatePowerSubstitution.eval_substitute]
  have HE : (fun j => (z ∘ F.scalar) j ^ weights S N m j) =
      (fun j => φ (F.scalarPrefix.basis.generator j)) := funext (fun j => (hφ j).symm)
  rw [HE]
  exact F.scalarPrefix.basis.representative_eval_algHom (H i) φ

theorem criticalStep_roots_interpret [Fintype ι] (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n)
    (z : (ι ⊕ Variables (n + 1)) → K)
    (hz : ∀ j, ((criticalStep F data).rows j).eval₂ (Int.castRingHom K) z = 0) :
    let x := fun i => z (ambient i) ^ physical S N m
    let mu := fun j => z (multiplier j) ^ ((data.degree - 1) * physical S N m)
    ∃ φ : F.scalarPrefix.carrier →ₐ[ℤ] K,
      (∀ i, (F.rows i).eval₂ (Int.castRingHom K) (z ∘ Sum.inl) = 0) ∧
      (∀ i, φ (F.scalarPrefix.basis.generator i) = z (Sum.inl (F.scalar i)) ^ weights S N m i) ∧
      (FermatCriticalHomogenization.polynomial data.low data.leading data.degree).eval₂ (Int.castRingHom K) x = 0 ∧
      (∀ i ∈ data.frozen, (∑ j, (Int.castRingHom K)
        (PhysicalPowerCriticalRows.coordinateNormals data.objective data.scales data.free i.succ j) * x j) = φ (data.heights i)) ∧
      (∀ i, (pderiv i (FermatCriticalHomogenization.polynomial data.low data.leading data.degree)).eval₂ (Int.castRingHom K) x =
        ∑ j, (Int.castRingHom K) (PhysicalPowerCriticalRows.coordinateNormals data.objective data.scales data.free j i) * mu j) ∧
      ∀ i, i ∉ data.frozen → mu i.succ = 0 := by
  dsimp only
  have hold := criticalStep_old_roots F data z hz
  obtain ⟨φ, hφ⟩ := F.interpret K (z ∘ Sum.inl) hold
  have Hnew : ∀ j, (PhysicalPowerCriticalRows.rows
      (FermatCriticalHomogenization.polynomial data.low data.leading data.degree) data.frozen
      (PhysicalPowerCriticalRows.coordinateNormals data.objective data.scales data.free)
      (historyHeights F data.heights) (fun _ => 1) data.degree (physical S N m) j).eval₂ (Int.castRingHom K) z = 0 :=
    fun j => hz (Sum.inr j)
  have HP := (PhysicalPowerCriticalRows.roots_iff_original (Int.castRingHom K) _ data.frozen _ _ _
    data.degree (physical S N m) z).mp Hnew
  have HE := (FlatAffineCriticalStage.roots_iff (Int.castRingHom K) _ data.frozen _ _ _).mp HP
  refine ⟨φ, hold, hφ, HE.1, ?_, HE.2.2⟩
  intro i hi
  apply (HE.2.1 i hi).trans
  simpa only [Function.comp_def, PhysicalPowerCriticalRows.point_parameter, pow_one] using
    historyHeights_eval F data.heights φ (z ∘ Sum.inl) hφ i

end LeanCanny.Algebra.IntegralHistorySampler
