/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPolynomialMap

/-! # Permuting exterior coordinates of the Koszul differential -/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def vectorPermutation (ρ : Equiv.Perm (Fin n)) :
    (Fin n → Poly n R) →ₗ[Poly n R] (Fin n → Poly n R) where
  toFun v := v ∘ ρ.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem vectorPermutation_single (ρ : Equiv.Perm (Fin n)) (i : Fin n) :
    vectorPermutation (R := R) ρ (Pi.single i 1) = Pi.single (ρ i) 1 := by
  funext j
  change (Pi.single i 1 : Fin n → Poly n R) (ρ.symm j) = (Pi.single (ρ i) 1 : Fin n → Poly n R) j
  by_cases hj : j = ρ i
  · subst j
    simp only [Equiv.symm_apply_apply, Pi.single_eq_same]
  · have hi : ρ.symm j ≠ i := fun hi => hj ((ρ.apply_symm_apply j).symm.trans (congrArg ρ hi))
    rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hj]

noncomputable def exteriorPermutation (ρ : Equiv.Perm (Fin n)) : Total n R →ₐ[Poly n R] Total n R :=
  ExteriorAlgebra.map (vectorPermutation ρ)

theorem exteriorPermutation_blade (ρ : Equiv.Perm (Fin n)) {k : ℕ} (v : Fin k → Fin n) :
    exteriorPermutation (R := R) ρ (blade (R := R) v) = blade (R := R) (ρ ∘ v) := by
  rw [exteriorPermutation, blade, ExteriorAlgebra.map_apply_ιMulti]
  congr 1
  funext j
  exact vectorPermutation_single ρ (v j)

theorem exteriorPermutation_wedge (ρ : Equiv.Perm (Fin n)) (i : Fin n) (x : Total n R) :
    exteriorPermutation (R := R) ρ (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) =
      KoszulExterior.wedge (Pi.single (ρ i) 1 : Fin n → Poly n R) (exteriorPermutation ρ x) := by
  change exteriorPermutation ρ (ExteriorAlgebra.ι (Poly n R) (Pi.single i 1) * x) = _
  rw [map_mul]
  change ExteriorAlgebra.map (vectorPermutation ρ) (ExteriorAlgebra.ι (Poly n R) (Pi.single i 1)) * _ = _
  rw [ExteriorAlgebra.map_apply_ι, vectorPermutation_single]
  rfl

theorem exteriorPermutation_differential_blade (ρ : Equiv.Perm (Fin n)) (p : Fin n → Poly n R)
    {k : ℕ} (v : Fin k → Fin n) :
    exteriorPermutation (R := R) ρ (KoszulExterior.differential p (blade (R := R) v)) =
      KoszulExterior.differential (p ∘ ρ.symm) (blade (R := R) (ρ ∘ v)) := by
  induction k with
  | zero =>
    simp only [blade_zero, KoszulExterior.differential, CliffordAlgebra.contractLeft_one, map_zero]
  | succ k ih =>
    rw [differential_blade_succ, map_sub, map_smul, exteriorPermutation_blade, exteriorPermutation_wedge, ih,
      differential_blade_succ]
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rfl

theorem exteriorPermutation_differential (ρ : Equiv.Perm (Fin n)) (p : Fin n → Poly n R) (x : Total n R) :
    exteriorPermutation (R := R) ρ (KoszulExterior.differential p x) =
      KoszulExterior.differential (p ∘ ρ.symm) (exteriorPermutation ρ x) := by
  have h : (exteriorPermutation (R := R) ρ).toLinearMap.comp (KoszulExterior.differential p) =
      (KoszulExterior.differential (p ∘ ρ.symm)).comp (exteriorPermutation ρ).toLinearMap := by
    apply (exteriorBasis (R := R)).ext
    intro s
    change exteriorPermutation ρ (KoszulExterior.differential p (exteriorBasis (R := R) s)) =
      KoszulExterior.differential (p ∘ ρ.symm) (exteriorPermutation ρ (exteriorBasis (R := R) s))
    rw [exteriorBasis_as_blade s rfl, exteriorPermutation_blade]
    exact exteriorPermutation_differential_blade ρ p _
  exact LinearMap.congr_fun h x

theorem exteriorPermutation_left_inverse (ρ : Equiv.Perm (Fin n)) (x : Total n R) :
    exteriorPermutation (R := R) ρ.symm (exteriorPermutation ρ x) = x := by
  have h : (exteriorPermutation (R := R) ρ.symm).toLinearMap.comp (exteriorPermutation ρ).toLinearMap = LinearMap.id := by
    apply (exteriorBasis (R := R)).ext
    intro s
    change exteriorPermutation ρ.symm (exteriorPermutation ρ (exteriorBasis (R := R) s)) = exteriorBasis (R := R) s
    rw [exteriorBasis_as_blade s rfl, exteriorPermutation_blade, exteriorPermutation_blade]
    congr 1
    funext j
    exact ρ.symm_apply_apply _
  exact LinearMap.congr_fun h x

end LeanCanny.Algebra.KoszulWeighted
