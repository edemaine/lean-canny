/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineValueGramSpace
public import LeanCanny.Algebra.ProjectiveValueGramHeight

/-! # Coefficient-height bounds from original affine rows and tests -/

@[expose] public section
namespace LeanCanny.Algebra.AffineValueGramBits
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma homogenized_mass_bound {n : ℕ} (p : MvPolynomial (Fin n) (Polynomial ℤ)) (D M : ℕ)
    (hp : ∀ u, coefficientMass (p.coeff u) ≤ M) (e : Fin (n + 1) →₀ ℕ) :
    coefficientMass ((rename AffineCoordinateSystem.layout
      (WeightedHomogenization.homogenize (fun _ => 1) D p)).coeff e) ≤ M := by
  by_cases hz : (rename AffineCoordinateSystem.layout
      (WeightedHomogenization.homogenize (fun _ => 1) D p)).coeff e = 0
  · simp [hz]
  · obtain ⟨v, hv, _⟩ := coeff_rename_ne_zero AffineCoordinateSystem.layout _ e hz
    rw [← hv, coeff_rename_mapDomain _ AffineCoordinateSystem.layout.injective, WeightedHomogenization.coefficient]
    split_ifs
    · exact hp _
    · simp

lemma Family.homogeneous_mass_bound (F : Family) (M : List Bool → ℕ)
    (hp : ∀ c i u, coefficientMass ((F.original c i).coeff u) ≤ M c)
    (c : List Bool) (i : Fin (F.homogeneous.layout.arity c)) (e : Fin (F.arity c + 1) →₀ ℕ) :
    coefficientMass ((F.homogeneous.original c i).coeff e) ≤ M c := by
  rw [F.homogeneous_original]
  exact homogenized_mass_bound _ _ _ (hp c i) e

theorem Family.mass_le (F : Family) (b : List Bool → ℕ)
    (hp : ∀ c i u, coefficientMass ((F.original c i).coeff u) ≤ 2 ^ b c) (c : List Bool) :
    NestedMass.mass (F.homogeneous.annihilator c) ≤
      2 ^ ProjectiveValueGram.massExponent (F.arity c) (F.width c) (b c) := by
  have hh := F.homogeneous_mass_bound (fun c => 2 ^ b c) hp c
  exact ProjectiveValueGram.annihilator_mass_le_two_pow _ _ _ _ _ _
    (fun i e => hh i.succ e) (fun e => hh ⟨0, F.homogeneous.positive c⟩ e)

theorem Family.height_le (F : Family) (b : List Bool → ℕ)
    (hp : ∀ c i u, coefficientMass ((F.original c i).coeff u) ≤ 2 ^ b c) (c : List Bool) (j k : ℕ) :
    ((((F.homogeneous.annihilator c).coeff j).coeff k).natAbs).size ≤
      ProjectiveValueGram.massExponent (F.arity c) (F.width c) (b c) + 1 := by
  have hh := F.homogeneous_mass_bound (fun c => 2 ^ b c) hp c
  exact ProjectiveValueGram.annihilator_height_le _ _ _ _ _ _
    (fun i e => hh i.succ e) (fun e => hh ⟨0, F.homogeneous.positive c⟩ e) j k

end LeanCanny.Algebra.AffineValueGramBits
