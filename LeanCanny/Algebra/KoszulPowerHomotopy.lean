/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCoefficientDivision

/-! # A polynomial coordinate homotopy for the pure-power system

Insert the chosen coordinate after dividing coefficient monomials by its
input power. The homotopy identity holds on each monomial exterior word
whose coefficient is divisible by that power or which already contains the
chosen coordinate. No coordinate inverses or field assumptions are used.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem differential_powers_succ (d : Fin n → ℕ) {k : ℕ} (v : Fin (k + 1) → Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.differential (Macaulay.powers (R := R) d) (monomialBlade (R := R) v m) =
      MvPolynomial.monomial (Finsupp.single (v 0) (d (v 0))) (1 : R) •
        monomialBlade (R := R) (Matrix.vecTail v) m -
      KoszulExterior.wedge (Pi.single (v 0) 1 : Fin n → Poly n R)
        (KoszulExterior.differential (Macaulay.powers (R := R) d)
          (monomialBlade (R := R) (Matrix.vecTail v) m)) := by
  rw [differential_monomialBlade_succ]
  congr 1
  change (MvPolynomial.monomial m (1 : R) * MvPolynomial.monomial (Finsupp.single (v 0) (d (v 0))) 1) • _ = _
  rw [monomialBlade, smul_smul, mul_comm]

theorem divide_powers_differential (d : Fin n → ℕ) (t m : Fin n →₀ ℕ) (ht : t ≤ m)
    {k : ℕ} (v : Fin k → Fin n) :
    divide (R := R) t (KoszulExterior.differential (Macaulay.powers (R := R) d) (monomialBlade (R := R) v m)) =
      KoszulExterior.differential (Macaulay.powers (R := R) d)
        (divide (R := R) t (monomialBlade (R := R) v m)) := by
  induction k with
  | zero => rw [differential_monomialBlade_zero, map_zero, divide_monomialBlade, ite_eq_left ht,
      differential_monomialBlade_zero]
  | succ k ih =>
    rw [differential_powers_succ, map_sub, divide_monomial_smul_of_le _ _ _ ht,
      divide_wedge, ih, divide_monomialBlade, ite_eq_left ht, divide_monomialBlade, ite_eq_left ht,
      differential_powers_succ]

theorem monomial_smul_divide_word (t m : Fin n →₀ ℕ) (ht : t ≤ m) {k : ℕ} (v : Fin k → Fin n) :
    MvPolynomial.monomial t (1 : R) • divide (R := R) t (monomialBlade (R := R) v m) =
      monomialBlade (R := R) v m := by
  rw [divide_monomialBlade, ite_eq_left ht, monomial_smul_monomialBlade, add_tsub_cancel_of_le ht]

theorem wedge_word_eq_zero_of_mem (i : Fin n) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ)
    (hi : i ∈ Set.range v) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (monomialBlade (R := R) v m) = 0 := by
  obtain ⟨j, hj⟩ := hi
  have hn : ¬Function.Injective (Fin.cons i v) := by
    intro hinj
    have he : (0 : Fin (k + 1)) = j.succ := hinj (by simp only [Fin.cons_zero, Fin.cons_succ, hj])
    exact Fin.succ_ne_zero j he.symm
  rw [wedge_monomialBlade, monomialBlade, blade_eq_zero_of_not_injective _ hn, smul_zero]

noncomputable def powerHomotopy (d : Fin n → ℕ) (i : Fin n) : Total n R →ₗ[R] Total n R :=
  ((KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)).restrictScalars R).comp
    (divide (R := R) (Finsupp.single i (d i)))

theorem powerHomotopy_apply (d : Fin n → ℕ) (i : Fin n) (x : Total n R) :
    powerHomotopy (R := R) d i x =
      KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (divide (R := R) (Finsupp.single i (d i)) x) := rfl

theorem powerHomotopy_identity_word (d : Fin n → ℕ) (i : Fin n) {k : ℕ} (v : Fin k → Fin n)
    (m : Fin n →₀ ℕ) (h : Finsupp.single i (d i) ≤ m ∨ i ∈ Set.range v) :
    KoszulExterior.differential (Macaulay.powers (R := R) d)
        (powerHomotopy (R := R) d i (monomialBlade (R := R) v m)) +
      powerHomotopy (R := R) d i
        (KoszulExterior.differential (Macaulay.powers (R := R) d) (monomialBlade (R := R) v m)) =
      monomialBlade (R := R) v m := by
  rcases h with ht | hi
  · have hh := KoszulExterior.homotopy_identity (Macaulay.powers (R := R) d)
      (Pi.single i 1 : Fin n → Poly n R) (divide (R := R) (Finsupp.single i (d i)) (monomialBlade (R := R) v m))
    rw [KoszulExterior.linearForm_single, ← divide_powers_differential d _ _ ht v] at hh
    change _ = Macaulay.powers (R := R) d i • _ at hh
    exact hh.trans (monomial_smul_divide_word _ _ ht v)
  · have hw := wedge_word_eq_zero_of_mem (R := R) i v m hi
    have hz : powerHomotopy (R := R) d i (monomialBlade (R := R) v m) = 0 := by
      rw [powerHomotopy_apply, ← divide_wedge, hw, map_zero]
    have hh := KoszulExterior.homotopy_identity (Macaulay.powers (R := R) d)
      (Pi.single i 1 : Fin n → Poly n R) (monomialBlade (R := R) v m)
    rw [hw, map_zero, zero_add, KoszulExterior.linearForm_single] at hh
    rw [hz, map_zero, zero_add, powerHomotopy_apply, ← divide_wedge, hh]
    exact divide_monomial_smul _ _

end LeanCanny.Algebra.KoszulWeighted
