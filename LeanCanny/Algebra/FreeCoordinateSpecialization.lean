/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Free coordinates followed by frozen coefficient inputs

The first `n` coordinates remain polynomial variables; every later input
becomes a coefficient. Free partial derivatives commute with this map,
including repeated derivatives. No degree or finiteness hypothesis is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.FreeCoordinateSpecialization
open MvPolynomial
open scoped Classical
variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

def environment (frozen : ℕ → S) (y : Fin n → S) (i : ℕ) : S :=
  if hi : i < n then y ⟨i, hi⟩ else frozen (i - n)

noncomputable def specialize (φ : R →+* S) (frozen : ℕ → S) :
    MvPolynomial ℕ R →+* MvPolynomial (Fin n) S :=
  eval₂Hom (C.comp φ) (fun i => if hi : i < n then X ⟨i, hi⟩ else C (frozen (i - n)))

theorem eval_specialize (φ : R →+* S) (frozen : ℕ → S) (p : MvPolynomial ℕ R) (y : Fin n → S) :
    (specialize φ frozen p).eval y = p.eval₂ φ (environment frozen y) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval_mul, eval₂_mul, hp, eval₂_X]
    congr 1
    by_cases hi : i < n <;> simp [specialize, environment, hi]

theorem specialize_pderiv_X (φ : R →+* S) (frozen : ℕ → S) (j : Fin n) (i : ℕ) :
    specialize φ frozen (pderiv j.val (X i)) = pderiv j (specialize φ frozen (X i)) := by
  by_cases hi : i < n
  · simp [specialize, pderiv_X, Pi.single_apply, hi, Fin.ext_iff]
  · have hij : i ≠ j.val := by omega
    simp [specialize, pderiv_X, hi, hij]

theorem specialize_pderiv (φ : R →+* S) (frozen : ℕ → S) (p : MvPolynomial ℕ R) (j : Fin n) :
    specialize φ frozen (pderiv j.val p) = pderiv j (specialize φ frozen p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [specialize]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [pderiv_mul, map_add, map_mul, hp, specialize_pderiv_X]

omit [CommRing S] in
theorem environment_at (x : ℕ → S) :
    environment (fun i => x (n + i)) (fun i : Fin n => x i.val) = x := by
  funext i
  by_cases hi : i < n
  · simp only [environment, hi, dite_true]
  · simp only [environment, hi, dite_false]
    rw [Nat.add_sub_of_le (Nat.le_of_not_lt hi)]

theorem eval_at (φ : R →+* S) (p : MvPolynomial ℕ R) (x : ℕ → S) :
    (specialize (n := n) φ (fun i => x (n + i)) p).eval (fun i => x i.val) = p.eval₂ φ x := by
  rw [eval_specialize, environment_at]

end LeanCanny.Algebra.FreeCoordinateSpecialization
