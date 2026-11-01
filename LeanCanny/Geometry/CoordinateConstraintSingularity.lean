/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedComponentSampling
/-! # Singular coordinate-constrained fibers have zero gradients in every free coordinate -/
@[expose] public section
namespace LeanCanny.Geometry.CoordinateConstraintSingularity
open Set LeanCanny.Algebra LeanCanny.Connectivity MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem outside_zero (p : MvPolynomial (Fin (n+1)) ℤ) (s : Finset (Fin (n+1)))
    (a : Fin (n+2) → Fin (n+1) → ℤ) (q : Fin (n+1) → ℤ) (hq : ∀ i, q i ≠ 0)
    (ha : ∀ j i, a j.succ i = if i = j then q j else 0) (y : Fin (n+1) → ℝ)
    (hp : p.eval₂ (Int.castRingHom ℝ) y = 0)
    (hs : ¬ Function.Surjective (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) p s a y)) :
    ∀ i, i ∉ s → (pderiv i p).eval₂ (Int.castRingHom ℝ) y = 0 := by
  let heights : Fin (n+1) → ℝ := fun j => ∑ i, (a j.succ i : ℝ) * y i
  have Hheights (c : s → ℝ) (H : ∀ i, ∑ j : s, c j * (a j.val.succ i : ℝ) = 0) : ∀ j, c j = 0 := by
    apply IntegralMixedSelectedComponentSampling.normal_independent s (fun i => (q i : ℝ))
      (fun i => Int.cast_ne_zero.mpr (hq i)) (0 : Fin (n+1)) c
    intro i
    have HE := H i
    simpa only [ha, Int.cast_ite, Int.cast_zero, PhysicalPowerCriticalRows.coordinateNormals, Fin.cons_succ] using HE
  obtain ⟨mu,Hmu,HR⟩ := FlatAffineSingularCriticalRoot.exists_stage_root_of_singular (Int.castRingHom ℝ) p s a
    (fun j => X j) heights y hp (fun _ _ => by simp only [eval₂_X, heights, Int.coe_castRingHom]) Hheights hs
  have HG := (FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) p s a (fun j => X j)
    (Sum.elim heights (Sum.elim y mu))).mp HR
  intro i hi
  have HE := HG.2.2.1 i
  have HU := HG.2.2.2 i hi
  change mu i.succ = 0 at HU
  change (pderiv i p).eval₂ (Int.castRingHom ℝ) y = ∑ j, (a j i : ℝ) * mu j at HE
  rw [Fin.sum_univ_succ, Hmu, mul_zero, zero_add] at HE
  have Hsum : (∑ j : Fin (n+1), (a j.succ i : ℝ) * mu j.succ) = (q i : ℝ) * mu i.succ := by
    simp [ha]
  rw [Hsum, HU, mul_zero] at HE
  exact HE

end LeanCanny.Geometry.CoordinateConstraintSingularity
