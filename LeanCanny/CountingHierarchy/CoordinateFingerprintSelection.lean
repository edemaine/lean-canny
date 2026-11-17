/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FingerprintIntegerRootLabels

/-! # A short tuple of fingerprint labels selects one algebraic point -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra
open scoped Classical

structure FingerprintLabelData where
  modulus : ℕ
  parameter : ℕ
  target : ℤ

def FingerprintLabelData.Bounded (D : ℕ) (L : FingerprintLabelData) : Prop :=
  2 < L.modulus ∧ L.modulus ≤ 2 * (D ^ 3 + 2) ∧ L.parameter < L.modulus ∧
    L.target.natAbs ≤ D * L.modulus

noncomputable def coordinateFingerprintSelection {n : ℕ} (P : Fin n → Polynomial ℤ)
    (D b : ℕ) (L : Fin n → FingerprintLabelData) (x : Fin n → ℝ) : Prop :=
  ∀ i, (P i).eval₂ (Int.castRingHom ℝ) (x i) = 0 ∧
    0 < (fingerprintIntegerRootLabel (P i) 1 D b (L i).modulus (L i).parameter (L i).target).eval₂
      (Int.castRingHom ℝ) (x i)

/-- Uniform coordinate degree and mass bounds suffice to select any prescribed
point in the product of the root sets. The tuple contains only three integers
per coordinate, even when those root sets have exponentially many elements. -/
theorem exists_coordinateFingerprintSelection {n : ℕ} (P : Fin n → Polynomial ℤ) (D b : ℕ)
    (hP : ∀ i, P i ≠ 0) (hD : ∀ i, (P i).natDegree ≤ D)
    (hbm : ∀ i, coefficientMass (P i) ≤ 2 ^ b) (a : Fin n → ℝ)
    (ha : ∀ i, (P i).eval₂ (Int.castRingHom ℝ) (a i) = 0) :
    ∃ L : Fin n → FingerprintLabelData, (∀ i, (L i).Bounded D) ∧
      ∀ x, coordinateFingerprintSelection P D b L x ↔ x = a := by
  have hmassOne : coefficientMass (1 : Polynomial ℤ) ≤ 2 ^ b := by
    change coefficientMass (Polynomial.C (1 : ℤ)) ≤ 2 ^ b
    rw [coefficientMass_C]
    change 1 ≤ 2 ^ b
    exact Nat.one_le_pow' b 1
  have hex (i : Fin n) := exists_fingerprintIntegerRootLabel (P i) 1 (hP i) D b (hD i)
    (by simp) (hbm i) hmassOne (a i) (ha i) (by simp)
  choose mu gamma target hp hmu2 hmub hg ht hval hneg using hex
  let L : Fin n → FingerprintLabelData := fun i => ⟨mu i, gamma i, target i⟩
  refine ⟨L, fun i => ⟨hmu2 i, hmub i, hg i, ht i⟩, fun x => ?_⟩
  constructor
  · intro hx
    funext i
    by_contra hne
    have hi := hneg i (x i) (hx i).1 hne
    have hp := (hx i).2
    change 0 < (fingerprintIntegerRootLabel (P i) 1 D b (mu i) (gamma i) (target i)).eval₂
      (Int.castRingHom ℝ) (x i) at hp
    linarith
  · rintro rfl i
    exact ⟨ha i, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (hval i)⟩

/-- For arbitrary labels, nonemptiness plus absence of a selected counterexample
already gives a good parameter. Soundness does not require checking isolation. -/
theorem exists_good_of_two_tests {A C Z : Type*} (selected : C → Prop) (parameter : C → A)
    (bad : A → Z → Prop) (hnonempty : ∃ c, selected c)
    (hnocounter : ¬∃ c z, selected c ∧ bad (parameter c) z) :
    ∃ x : A, ∀ z, ¬bad x z := by
  obtain ⟨c, hc⟩ := hnonempty
  exact ⟨parameter c, fun z hz => hnocounter ⟨c, z, hc, hz⟩⟩

end LeanCanny.CountingHierarchy
