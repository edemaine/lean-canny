/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerOriginal

/-! # Prefixes of multiplier-power towers

Earlier blocks and their equations embed in a later tower by their original
indices. This applies to every root, including singular roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {n d k : ℕ}

def prefixIndex (hd : d ≤ k) : Index n d → Index n k :=
  Fin.castLE (Nat.mul_le_mul_right (width n) hd)

lemma prefixIndex_row (hd : d ≤ k) (t : Fin d) (j : Variables n) :
    prefixIndex hd (rowEquiv n d (t, j)) = rowEquiv n k (Fin.castLE hd t, j) := by
  apply Fin.ext
  rfl

lemma prefixIndex_current (hd : d ≤ k) (t : Fin d) (i : Fin n) :
    prefixIndex hd (current t i) = current (Fin.castLE hd t) i := prefixIndex_row hd t (Sum.inl i)

lemma prefixIndex_multiplier (hd : d ≤ k) (t : Fin d) (r : Fin (n + 1)) :
    prefixIndex hd (multiplier t r) = multiplier (Fin.castLE hd t) r := prefixIndex_row hd t (Sum.inr r)

lemma powerPoint_prefix {K : Type*} [Monoid K] (hd : d ≤ k) (D : ℕ) (z : Index n k → K) :
    powerPoint D (z ∘ prefixIndex hd) = powerPoint D z ∘ prefixIndex hd := by
  funext i
  obtain ⟨⟨t, j⟩, rfl⟩ := (rowEquiv n d).surjective i
  simp only [Function.comp_apply, prefixIndex_row, powerPoint, Equiv.symm_apply_apply]

lemma rename_prefix_height (hd : d ≤ k) (t : Fin d) (a : Fin n → ℤ) :
    rename (prefixIndex hd) (height t a) = height (Fin.castLE hd t) a := by
  simp only [height, map_sum, map_mul, rename_C, rename_X, prefixIndex_current]

lemma rename_prefix_level (hd : d ≤ k) (t : Fin d) (b : Level n t.val ℤ) :
    rename (prefixIndex hd) (levelPolynomial t b) = levelPolynomial (Fin.castLE hd t) b := by
  cases b with
  | constant c => simp only [levelPolynomial, levelLinear, levelConstant, zero_add, rename_C]
  | height j a =>
    simp only [levelPolynomial, levelLinear, levelConstant, map_zero, add_zero, rename_prefix_height]
    rfl
  | midpoint l r a =>
    simp only [levelPolynomial, levelLinear, levelConstant, map_zero, add_zero, map_add, rename_prefix_height]
    rfl

lemma rename_prefix_row (hd : d ≤ k) (p : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (t : ℕ) → Fin n → Level n t ℤ) (t : Fin d) (j : Variables n) :
    rename (prefixIndex hd) (row p D (fun t : Fin d => s t.val) (fun t => a t.val)
      (fun t => b t.val) t j) =
    row p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) (Fin.castLE hd t) j := by
  have hc : prefixIndex hd ∘ current (n := n) t = current (Fin.castLE hd t) :=
    funext (prefixIndex_current hd t)
  cases j with
  | inl i =>
    simp only [row, gradient, map_sub, map_sum, map_mul, map_pow, rename_C, rename_X,
      rename_rename, hc, prefixIndex_multiplier, Fin.val_castLE]
  | inr r =>
    refine Fin.cases ?_ (fun j => ?_) r
    · simp only [row, Fin.cases_zero, rename_rename, hc]
    · simp only [row, Fin.cases_succ, Fin.val_castLE]
      split_ifs
      · rw [map_sub, rename_prefix_height, rename_prefix_level]
      · rw [rename_X, prefixIndex_multiplier]

lemma rename_prefix_system (hd : d ≤ k) (p : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (t : ℕ) → Fin n → Level n t ℤ) (i : Index n d) :
    rename (prefixIndex hd) (system p D (fun t : Fin d => s t.val) (fun t => a t.val)
      (fun t => b t.val) i) =
    system p D (fun t : Fin k => s t.val) (fun t => a t.val) (fun t => b t.val) (prefixIndex hd i) := by
  obtain ⟨⟨t, j⟩, rfl⟩ := (rowEquiv n d).surjective i
  rw [prefixIndex_row, system_row, system_row, rename_prefix_row]

theorem roots_prefix {K : Type*} [CommRing K] (phi : ℤ →+* K) (hd : d ≤ k)
    (p : MvPolynomial (Fin n) ℤ) (D : ℕ) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (t : ℕ) → Fin n → Level n t ℤ)
    (z : Index n k → K)
    (hz : ∀ i, (system p D (fun t : Fin k => s t.val) (fun t => a t.val)
      (fun t => b t.val) i).eval₂ phi z = 0) :
    ∀ i, (system p D (fun t : Fin d => s t.val) (fun t => a t.val)
      (fun t => b t.val) i).eval₂ phi (z ∘ prefixIndex hd) = 0 := by
  intro i
  rw [← eval₂_rename, rename_prefix_system]
  exact hz _

end LeanCanny.Algebra.FlatAffinePowerTower
