/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLevelProgram

/-! # Actual tower level semantics of the shared writer -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelProgram
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open scoped Classical BigOperators

theorem value_eq_level (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (r : Fin (FlatAffineFullSourceTower.arity F u)) (x : ℕ → ℂ)
    (z : FlatAffineCriticalTower.Ancestors (FlatAffineFullSourceTower.arity F u) k → ℂ)
    (hp : ∀ j : Fin k, ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      x (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        z (FlatAffineCriticalTower.oldAmbient k j i)) :
    AffineLevel.value (inputs F base ancestor u k r.val) x =
      (FlatAffineFullSourceTower.level F u k r).polynomial.eval₂ (Int.castRingHom ℂ) z := by
  let bits := F.level (FlatAffineFullSourceTower.levelQuery u k r.val)
  change AffineLevel.value (FlatAffineLevelRecord.fromRecord (base u) (ancestor u)
    (FlatAffineFullSourceTower.arity F u) (F.width u) k bits) x = _
  rw [FlatAffineLevelRecord.record_value]
  by_cases hk : 0 < k
  · let a : Fin (FlatAffineFullSourceTower.arity F u) → ℤ :=
      fun i => FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.normal bits) i.val
    let l : Fin k := ⟨FlatAffineLevelRecord.leftStage k bits, by have H : FlatAffineLevelRecord.leftStage k bits ≤ k - 1 := Nat.min_le_right _ _; omega⟩
    let v : Fin k := ⟨FlatAffineLevelRecord.rightStage k bits, by have H : FlatAffineLevelRecord.rightStage k bits ≤ k - 1 := Nat.min_le_right _ _; omega⟩
    have hlevel : FlatAffineFullSourceTower.level F u k r =
        if FlatAffineFullSourceTower.tag bits = 1 then .height l a
        else if FlatAffineFullSourceTower.tag bits = 2 then .midpoint l v a
        else .constant (FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.constant bits) 0) := by
      unfold FlatAffineFullSourceTower.level
      dsimp only
      rw [dite_eq_left hk]
    have hl : (∑ i ∈ Finset.range (FlatAffineFullSourceTower.arity F u),
        (FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.normal bits) i : ℂ) *
          x (ancestor u + FlatAffineLevelRecord.leftStage k bits * FlatAffineFullSourceTower.stageWidth F u + i)) =
        (AffineHeightPolynomial.polynomial a (FlatAffineCriticalTower.oldAmbient k l)).eval₂ (Int.castRingHom ℂ) z := by
      rw [AffineHeightPolynomial.eval, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg₂ (· * ·) rfl (hp l i)
    have hv : (∑ i ∈ Finset.range (FlatAffineFullSourceTower.arity F u),
        (FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.normal bits) i : ℂ) *
          x (ancestor u + FlatAffineLevelRecord.rightStage k bits * FlatAffineFullSourceTower.stageWidth F u + i)) =
        (AffineHeightPolynomial.polynomial a (FlatAffineCriticalTower.oldAmbient k v)).eval₂ (Int.castRingHom ℂ) z := by
      rw [AffineHeightPolynomial.eval, ← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg₂ (· * ·) rfl (hp v i)
    rw [hlevel]
    simp only [hk, true_and]
    by_cases ht1 : FlatAffineFullSourceTower.tag bits = 1
    · simpa only [ht1, ite_true, FlatAffineCriticalTower.Level.polynomial, FlatAffineFullSourceTower.stageWidth] using hl
    · by_cases ht2 : FlatAffineFullSourceTower.tag bits = 2
      · simpa only [ht1, ht2, show (2 : ℕ) ≠ 1 by decide, ite_false, ite_true, FlatAffineCriticalTower.Level.polynomial, FlatAffineFullSourceTower.stageWidth,
          AffineHeightPolynomial.midpointLevel, eval₂_add] using congrArg₂ (· + ·) hl hv
      · simp only [ht1, ht2, ite_false, FlatAffineCriticalTower.Level.polynomial, eval₂_C, Int.coe_castRingHom]
  · unfold FlatAffineFullSourceTower.level
    dsimp only
    rw [dite_eq_right hk]
    simp only [hk, false_and, ite_false, FlatAffineCriticalTower.Level.polynomial, eval₂_C, Int.coe_castRingHom, bits]

theorem output_eq_level (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (r : Fin (FlatAffineFullSourceTower.arity F u)) (env : ℕ → ℂ)
    (hg : ∀ g ∈ AffineLevel.packedGates (inputs F base ancestor u k r.val), g.Holds env)
    (z : FlatAffineCriticalTower.Ancestors (FlatAffineFullSourceTower.arity F u) k → ℂ)
    (hp : ∀ j : Fin k, ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      env (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        z (FlatAffineCriticalTower.oldAmbient k j i)) :
    env (AffineLevel.packedOutput (inputs F base ancestor u k r.val)) =
      (FlatAffineFullSourceTower.level F u k r).polynomial.eval₂ (Int.castRingHom ℂ) z :=
  (AffineLevel.packed_output_sound _ env hg).trans (value_eq_level F base ancestor u k r env z hp)

end LeanCanny.Encoding.FlatAffineLevelProgram
