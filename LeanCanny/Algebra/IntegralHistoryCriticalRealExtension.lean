/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralHistoryRelativeCritical

/-! # Real attachment of an actual physical critical block

Only the newly introduced coordinates receive odd-power roots. The old physical
sample and its interpreting hom remain fixed, including at singular critical
points. The parity assumption is explicit; it holds for the even Fermat sources.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial FlatAffineCriticalStage UniformIntegralPowerSchedule
open scoped Classical BigOperators
variable {S N m n : ℕ} {ι : Type} [Fintype ι]

theorem criticalStep_real_extend (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n)
    (hd : Odd (data.degree-1)) (z : ι → ℝ)
    (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : F.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (F.scalarPrefix.basis.generator i)=z (F.scalar i)^weights S N m i)
    (y : Fin (n+1) → ℝ) (mu : Fin (n+2) → ℝ)
    (hp : (FermatCriticalHomogenization.polynomial data.low data.leading data.degree).eval₂ (Int.castRingHom ℝ) y=0)
    (hh : ∀ i ∈ data.frozen, (data.scales i:ℝ)*y i=φ (data.heights i))
    (hg : ∀ i, (pderiv i (FermatCriticalHomogenization.polynomial data.low data.leading data.degree)).eval₂
      (Int.castRingHom ℝ) y=∑ j, (Int.castRingHom ℝ)
        (PhysicalPowerCriticalRows.coordinateNormals data.objective data.scales data.free j i)*mu j)
    (hi : ∀ i, i ∉ data.frozen → mu i.succ=0) :
    ∃ w : (ι ⊕ Variables (n+1)) → ℝ,
      (∀ i, ((criticalStep F data).rows i).eval₂ (Int.castRingHom ℝ) w=0) ∧
      (∀ i, w (Sum.inl i)=z i) ∧
      (∀ i, w (ambient i)^physical S N m=y i) ∧
      (∀ i, w (multiplier i)^((data.degree-1)*physical S N m)=mu i) := by
  have ha : ∀ i, ∃ a : ℝ, a^physical S N m=y i := fun i =>
    FlatAffinePowerTower.real_pow_surjective _ (physical_odd S N m) (y i)
  have hb : ∀ i, ∃ b : ℝ, b^((data.degree-1)*physical S N m)=mu i := fun i =>
    FlatAffinePowerTower.real_pow_surjective _ (hd.mul (physical_odd S N m)) (mu i)
  choose a ha using ha
  choose b hb using hb
  let w : (ι ⊕ Variables (n+1)) → ℝ := Sum.elim z (Sum.elim a b)
  have hw : PhysicalPowerCriticalRows.point (fun _ : ι => 1) data.degree (physical S N m) w=
      Sum.elim z (Sum.elim y mu) := by
    funext i
    cases i with
    | inl i => simp [PhysicalPowerCriticalRows.point,PhysicalPowerCriticalRows.powers,w]
    | inr i =>
      cases i with
      | inl i => exact ha i
      | inr i => exact hb i
  refine ⟨w,?_,fun _ => rfl,ha,hb⟩
  apply (TriangularPolynomialSystem.roots_append (Int.castRingHom ℝ) _ _ w).mpr
  refine ⟨hz,?_⟩
  apply (PhysicalPowerCriticalRows.roots_iff_original (Int.castRingHom ℝ) _ _ _ _ _ _ _ w).mpr
  rw [hw]
  apply (FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) _ _ _ _ _).mpr
  refine ⟨hp,?_,hg,hi⟩
  intro i hif
  have HE := PhysicalPowerCriticalRows.normal_height_sum (Int.castRingHom ℝ)
    data.objective data.scales data.free i y 1
  simp only [pow_one] at HE
  exact HE.trans ((hh i hif).trans (historyHeights_eval F data.heights φ z hφ i).symm)

omit [Fintype ι] in
/-- Coordinate criticality supplies all multipliers without a regularity premise. -/
theorem coordinate_multipliers (F : Sampler S N m ι) (data : CriticalData F.scalarPrefix n) (y : Fin (n+1) → ℝ)
    (hg : ∀ i, i ∉ data.frozen → i≠data.free →
      (pderiv i (FermatCriticalHomogenization.polynomial data.low data.leading data.degree)).eval₂
        (Int.castRingHom ℝ) y=0) :
    ∃ mu : Fin (n+2) → ℝ,
      (∀ i, (pderiv i (FermatCriticalHomogenization.polynomial data.low data.leading data.degree)).eval₂
        (Int.castRingHom ℝ) y=∑ j, (Int.castRingHom ℝ)
          (PhysicalPowerCriticalRows.coordinateNormals data.objective data.scales data.free j i)*mu j) ∧
      ∀ i, i ∉ data.frozen → mu i.succ=0 := by
  let g := fun i => (pderiv i (FermatCriticalHomogenization.polynomial data.low data.leading data.degree)).eval₂
    (Int.castRingHom ℝ) y
  let mu : Fin (n+2) → ℝ := Fin.cons (g data.free/(data.objective:ℝ))
    (fun i => if i ∈ data.frozen then g i/(data.scales i:ℝ) else 0)
  have ho : (data.objective:ℝ)≠0 := Int.cast_ne_zero.mpr data.objective_ne
  have hs : ∀ i, (data.scales i:ℝ)≠0 := fun i => Int.cast_ne_zero.mpr (data.scales_ne i)
  refine ⟨mu,?_,?_⟩
  · intro i
    have HE := PhysicalPowerCriticalRows.normal_power_sum (Int.castRingHom ℝ)
      data.objective data.scales data.free i mu 1
    simp only [pow_one] at HE
    rw [HE]
    by_cases hf : i=data.free
    · subst i
      simp only [mu,Fin.cons_zero,Fin.cons_succ,data.free_not_frozen,ite_false,ite_true,mul_zero,add_zero]
      exact (mul_div_cancel₀ (g data.free) ho).symm
    · by_cases hi : i ∈ data.frozen
      · simp only [mu,Fin.cons_succ,hf,ite_false,hi,ite_true,zero_add]
        exact (mul_div_cancel₀ (g i) (hs i)).symm
      · simp only [mu,Fin.cons_succ,hf,hi,ite_false,mul_zero,add_zero]
        exact hg i hi hf
  · intro i hi
    simp only [mu,Fin.cons_succ,hi,ite_false]

end LeanCanny.Algebra.IntegralHistorySampler
