/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerResidue

/-! # Coefficient-ring specialization of the finite residue functional -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical BigOperators

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

theorem map_degree_le (φ : S →+* T) (v : MvPolynomial (Fin n) S) :
    (v.map φ).totalDegree ≤ v.totalDegree :=
  Finset.sup_mono (MvPolynomial.support_map_subset φ v)

theorem truncated_map (φ : S →+* T) (ell B : ℕ)
    (r : Fin n → MvPolynomial (Fin n) S) (v : MvPolynomial (Fin n) S) :
    φ (truncated ell r B v) = truncated ell (fun i => (r i).map φ) B (v.map φ) := by
  change φ (∑ j ∈ indices n B, term ell r v j) =
    ∑ j ∈ indices n B, term ell (fun i => (r i).map φ) (v.map φ) j
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold term
  rw [← MvPolynomial.coeff_map φ]
  congr 1
  simp only [map_mul, map_prod, map_pow]

/-- Specialization needs no nonsingularity or squarefreeness hypothesis. -/
theorem residue_map (φ : S →+* T) {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) :
    φ (residue ell r v) = residue ell (fun i => (r i).map φ) (v.map φ) := by
  have hr' (i : Fin n) : ((r i).map φ).totalDegree < ell :=
    (map_degree_le φ (r i)).trans_lt (hr i)
  calc
    _ = truncated ell (fun i => (r i).map φ) v.totalDegree (v.map φ) :=
      truncated_map φ ell v.totalDegree r v
    _ = _ := (residue_eq_truncated hell (fun i => (r i).map φ) hr'
      (v.map φ) (map_degree_le φ v)).symm

end LeanCanny.CountingHierarchy.PurePowerResidue
