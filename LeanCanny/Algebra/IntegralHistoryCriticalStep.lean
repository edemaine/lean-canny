/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistorySampler
public import LeanCanny.Algebra.PhysicalPowerCriticalAppend

/-! # Retaining complete coordinate-critical histories

A new critical block reads the actual canonical scalar heights, powered
before embedding them in the full history. All older equations and physical
coordinates remain. The scalar slots keep their original powers, and the
new block preserves exclusion at infinity without a regularity assumption.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial WeightedHomogenization UniformIntegralPowerSchedule FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m n : ℕ} {ι : Type}

structure CriticalData (P : UniformIntegralPrefix.Prefix S N m) (n : ℕ) where
  heights : Fin (n + 1) → P.carrier
  low : MvPolynomial (Fin (n + 1)) ℤ
  leading : ℤ
  objective : ℤ
  scales : Fin (n + 1) → ℤ
  frozen : Finset (Fin (n + 1))
  free : Fin (n + 1)
  degree : ℕ
  birth_bound : m ≤ S
  degree_two : 2 ≤ degree
  low_degree : low.totalDegree < degree
  leading_ne : leading ≠ 0
  objective_ne : objective ≠ 0
  scales_ne : ∀ i, scales i ≠ 0
  free_not_frozen : free ∉ frozen

noncomputable def historyHeights (F : Sampler S N m ι) (H : Fin (n + 1) → F.scalarPrefix.carrier) :
    Fin (n + 1) → MvPolynomial ι ℤ := fun i =>
  rename F.scalar (CoordinatePowerSubstitution.substitute (weights S N m) (F.scalarPrefix.basis.representative (H i)))

private theorem substitute_one {κ : Type*} (p : MvPolynomial κ ℤ) :
    CoordinatePowerSubstitution.substitute (fun _ => 1) p = p := by
  induction p using MvPolynomial.induction_on with
  | C a => exact CoordinatePowerSubstitution.substitute_C _ a
  | add p q hp hq => rw [map_add, hp, hq]
  | mul_X p i hp => rw [map_mul, hp, CoordinatePowerSubstitution.substitute_X, pow_one]

theorem historyHeights_degree (F : Sampler S N m ι) (hm : m ≤ S)
    (H : Fin (n + 1) → F.scalarPrefix.carrier) (i : Fin (n + 1)) :
    (CoordinatePowerSubstitution.substitute (fun _ => 1) (historyHeights F H i)).totalDegree < physical S N m := by
  rw [substitute_one]
  exact (totalDegree_rename_le _ _).trans_lt (physical_representative_degree S hm F.scalarPrefix.basis (H i))

noncomputable def criticalStep [Fintype ι] (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n) :
    Sampler S N m (ι ⊕ Variables (n + 1)) where
  scalarPrefix := F.scalarPrefix
  scalar := Sum.inl ∘ F.scalar
  rows := PhysicalPowerCriticalAppend.rows F.rows data.low data.leading data.objective data.scales
    data.frozen data.free (historyHeights F data.heights) (fun _ => 1) data.degree (physical S N m)
  degrees := PhysicalPowerCriticalAppend.degrees F.degrees data.frozen data.degree (physical S N m)
  row_degree := PhysicalPowerCriticalAppend.row_degree F.rows F.degrees F.row_degree data.low
    data.leading data.objective data.scales data.frozen data.free _ _ data.degree (physical S N m)
    data.degree_two (physical_pos S N m) data.low_degree (fun i _ => historyHeights_degree F data.birth_bound data.heights i)
  degree_pos := by
    intro i
    cases i with
    | inl j => exact F.degree_pos j
    | inr j =>
      exact PhysicalPowerCriticalRows.degrees_pos data.frozen data.degree (physical S N m)
        data.degree_two (physical_pos S N m) j
  noInfinity := by
    apply PhysicalPowerCriticalAppend.noInfinity (Int.castRingHom ℂ) F.rows F.degrees F.noInfinity
      data.low data.leading data.objective data.scales data.frozen data.free data.free_not_frozen
      _ _ data.degree (physical S N m) data.degree_two (physical_pos S N m) data.low_degree
    · change (data.leading : ℂ) ≠ 0
      exact_mod_cast data.leading_ne
    · change (data.objective : ℂ) ≠ 0
      exact_mod_cast data.objective_ne
    · intro i
      change (data.scales i : ℂ) ≠ 0
      exact_mod_cast data.scales_ne i
    · intro i _
      exact historyHeights_degree F data.birth_bound data.heights i
  interpret := by
    intro K instK z hz
    apply F.interpret K (z ∘ Sum.inl)
    intro i
    have HI := hz (Sum.inl i)
    simpa only [PhysicalPowerCriticalAppend.rows, TriangularPolynomialSystem.append,
      Sum.elim_inl, eval₂_rename] using HI

theorem criticalStep_old_roots [Fintype ι] {K : Type*} [CommRing K]
    (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n) (z : (ι ⊕ Variables (n + 1)) → K)
    (hz : ∀ j, ((criticalStep F data).rows j).eval₂ (Int.castRingHom K) z = 0) :
    ∀ i, (F.rows i).eval₂ (Int.castRingHom K) (z ∘ Sum.inl) = 0 := by
  intro i
  have HI := hz (Sum.inl i)
  simpa only [criticalStep, PhysicalPowerCriticalAppend.rows, TriangularPolynomialSystem.append,
    Sum.elim_inl, eval₂_rename] using HI

end LeanCanny.Algebra.IntegralHistorySampler
