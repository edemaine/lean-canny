/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout

/-! # Collected coefficients after embedding a polynomial in a variable block

Exponent vectors using variables outside the selected block have coefficient
zero. Otherwise the coefficient is exactly that of the restricted exponent
vector in the original polynomial, including empty blocks.
-/

@[expose] public section
namespace LeanCanny.Algebra.BlockRenameCoefficient
open MvPolynomial
open scoped Classical

def shift (A N O : ℕ) (hfit : O + A ≤ N) (i : Fin A) : Fin N := ⟨O + i.val, by omega⟩

theorem shift_injective (A N O : ℕ) (hfit : O + A ≤ N) : Function.Injective (shift A N O hfit) := by
  intro i j h
  apply Fin.ext
  have H := congrArg Fin.val h
  simp only [shift] at H
  omega

noncomputable def restrict (A N O : ℕ) (hfit : O + A ≤ N) (m : Fin N →₀ ℕ) : Fin A →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => m (shift A N O hfit i))

def Supported (A N O : ℕ) (m : Fin N →₀ ℕ) : Prop :=
  ∀ j, (O ≤ j.val ∧ j.val < O + A) ∨ m j = 0

theorem map_restrict (A N O : ℕ) (hfit : O + A ≤ N) (m : Fin N →₀ ℕ) (hm : Supported A N O m) :
    (restrict A N O hfit m).mapDomain (shift A N O hfit) = m := by
  ext j
  by_cases hi : O ≤ j.val ∧ j.val < O + A
  · let i : Fin A := ⟨j.val - O, by omega⟩
    have he : shift A N O hfit i = j := Fin.ext (by dsimp [shift, i]; omega)
    rw [← he, Finsupp.mapDomain_apply_of_injective (shift_injective A N O hfit)]
    rfl
  · have hout : j ∉ Set.range (shift A N O hfit) := by
      rintro ⟨i, he⟩
      apply hi
      have H := congrArg Fin.val he
      dsimp only [shift] at H
      have := i.isLt
      omega
    rw [Finsupp.mapDomain_of_notMem_range _ _ hout, (hm j).resolve_left hi]

theorem coefficient {R : Type*} [CommSemiring R] (A N O : ℕ) (hfit : O + A ≤ N)
    (p : MvPolynomial (Fin A) R) (m : Fin N →₀ ℕ) :
    (rename (shift A N O hfit) p).coeff m =
      if Supported A N O m then p.coeff (restrict A N O hfit m) else 0 := by
  by_cases hm : Supported A N O m
  · rw [ite_eq_left hm]
    conv_lhs => rw [← map_restrict A N O hfit m hm]
    exact coeff_rename_mapDomain _ (shift_injective A N O hfit) _ _
  · rw [ite_eq_right hm]
    apply coeff_rename_eq_zero
    intro v hv
    apply False.elim
    apply hm
    intro j
    by_cases hi : O ≤ j.val ∧ j.val < O + A
    · exact Or.inl hi
    · right
      rw [← hv]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨i, he⟩
      apply hi
      have H := congrArg Fin.val he
      dsimp only [shift] at H
      have := i.isLt
      omega

end LeanCanny.Algebra.BlockRenameCoefficient
