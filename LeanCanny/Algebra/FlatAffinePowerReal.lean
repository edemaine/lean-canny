/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerOriginal
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # Odd multiplier powers preserve every real original root

Odd powers are bijective on the reals. Ambient coordinates stay fixed, and
the power tower and original Lagrange tower therefore have equivalent real
root sets, with no regularity assumption.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

lemma real_pow_surjective (e : ℕ) (he : Odd e) : Function.Surjective (fun x : ℝ => x ^ e) := by
  have hne : e ≠ 0 := by intro h; subst e; simp at he
  have hnonneg (x : ℝ) (hx : 0 ≤ x) : ∃ y : ℝ, y ^ e = x := by
    obtain ⟨y, hy⟩ := (NNReal.powOrderIso e hne).surjective ⟨x, hx⟩
    exact ⟨y, congrArg (fun z : NNReal => (z : ℝ)) hy⟩
  intro x
  by_cases hx : 0 ≤ x
  · exact hnonneg x hx
  · obtain ⟨y, hy⟩ := hnonneg (-x) (by linarith)
    refine ⟨-y, ?_⟩
    change (-y) ^ e = x
    rw [he.neg_pow, hy, neg_neg]

lemma real_powerPoint_injective (D : ℕ) (hodd : Odd (D - 1)) :
    Function.Injective (powerPoint (n := n) (k := k) (K := ℝ) D) := by
  intro x y h
  funext j
  have hj := congrFun h j
  unfold powerPoint at hj
  cases hr : ((rowEquiv n k).symm j).2 with
  | inl i => simpa only [hr] using hj
  | inr r => exact hodd.pow_injective (by simpa only [hr] using hj)

lemma real_powerPoint_surjective (D : ℕ) (hodd : Odd (D - 1)) :
    Function.Surjective (powerPoint (n := n) (k := k) (K := ℝ) D) := by
  intro x
  choose nu hnu using fun j => real_pow_surjective (D - 1) hodd (x j)
  let z : Index n k → ℝ := fun j => match ((rowEquiv n k).symm j).2 with
    | .inl _ => x j
    | .inr _ => nu j
  refine ⟨z, ?_⟩
  funext j
  unfold powerPoint
  cases hj : ((rowEquiv n k).symm j).2 with
  | inl i => simp only [z, hj]
  | inr r => simpa only [z, hj] using hnu j

noncomputable def realPowerEquiv (D : ℕ) (hodd : Odd (D - 1)) :
    (Index n k → ℝ) ≃ (Index n k → ℝ) :=
  Equiv.ofBijective (powerPoint D) ⟨real_powerPoint_injective D hodd, real_powerPoint_surjective D hodd⟩

noncomputable def realRootEquiv (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : 1 < D) (hodd : Odd (D - 1))
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ) :
    {z : Index n k → ℝ // ∀ i,
      (system p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) i).eval₂ (Int.castRingHom ℝ) z = 0} ≃
    {z : Index n k → ℝ // ∀ i, (FlatAffineCriticalTower.system p s a b k i).eval₂ (Int.castRingHom ℝ) z = 0} :=
  (realPowerEquiv D hodd).subtypeEquiv (roots_iff_original (Int.castRingHom ℝ) p D hD s a b)

end LeanCanny.Algebra.FlatAffinePowerTower
