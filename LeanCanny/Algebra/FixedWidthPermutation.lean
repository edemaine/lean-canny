/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomial
public import Mathlib.Data.Finsupp.Basic

/-! # Spatial permutations of fixed-width monomial ranks -/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthPolynomial
variable {n : ℕ}

noncomputable def permutationIndex (W : ℕ) (ρ : Equiv.Perm (Fin n)) (r : Fin (count n W)) : Fin (count n W) :=
  index n W (Finsupp.equivMapDomain ρ (vector n W r)) (fun i => by
    rw [Finsupp.equivMapDomain_apply]
    exact vector_lt n W r (ρ.symm i))

theorem vector_permutationIndex (W : ℕ) (ρ : Equiv.Perm (Fin n)) (r : Fin (count n W)) :
    vector n W (permutationIndex W ρ r) = Finsupp.equivMapDomain ρ (vector n W r) :=
  vector_index n W _ _

theorem permutationIndex_left_inverse (W : ℕ) (ρ : Equiv.Perm (Fin n)) (r : Fin (count n W)) :
    permutationIndex W ρ.symm (permutationIndex W ρ r) = r := by
  apply vector_injective n W
  rw [vector_permutationIndex, vector_permutationIndex]
  ext i
  simp only [Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

noncomputable def permutation (W : ℕ) (ρ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (count n W)) :=
  Equiv.ofBijective (permutationIndex W ρ)
    ⟨by
      intro r s he
      have hi := congrArg (permutationIndex W ρ.symm) he
      simpa only [permutationIndex_left_inverse] using hi,
      fun r => ⟨permutationIndex W ρ.symm r, by
        simpa only [Equiv.symm_symm] using permutationIndex_left_inverse W ρ.symm r⟩⟩

theorem vector_permutation (W : ℕ) (ρ : Equiv.Perm (Fin n)) (r : Fin (count n W)) :
    vector n W (permutation W ρ r) = Finsupp.equivMapDomain ρ (vector n W r) :=
  vector_permutationIndex W ρ r

end LeanCanny.Algebra.FixedWidthPolynomial
