/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinatePowerRegularity
public import LeanCanny.Algebra.ProjectiveNullstellensatz
public import Mathlib.Data.List.FinRange

/-! # Full-length ambient regular sequences inside projective input ideals

Coordinate-power membership supplies a regular sequence of length equal
to the number of variables, contained in the ideal. The projective
Nullstellensatz supplies that membership when there is no nonzero common
root over an algebraically closed field. This regular sequence consists
of coordinate powers, not the original input forms.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectiveRegularSequence
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]

theorem exists_regular_sequence_in_ideal (I : Ideal (MvPolynomial (Fin n) R))
    (hI : ∀ j : Fin n, ∃ N : ℕ, (MvPolynomial.X j : MvPolynomial (Fin n) R) ^ N ∈ I) :
    ∃ rs : List (MvPolynomial (Fin n) R), rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) R) rs := by
  choose N hN using hI
  let d : Fin n → ℕ := fun i => N i + 1
  let rs := (List.finRange n).map (fun i => (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ d i)
  have hp (i : Fin n) : (MvPolynomial.X i : MvPolynomial (Fin n) R) ^ d i ∈ I := by
    simpa only [d, pow_succ'] using I.mul_mem_left (MvPolynomial.X i) (hN i)
  refine ⟨rs, ?_, ?_, ?_⟩
  · simp only [rs, List.length_map, List.length_finRange]
  · intro r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact hp i
  · exact CoordinatePowerRegularity.isRegular_map_powers d (List.finRange n) (List.nodup_finRange n)
      (fun _ _ => Nat.zero_lt_succ _)

theorem exists_regular_sequence_of_no_nonzero_root {K ι : Type*} [Field K] [IsAlgClosed K]
    (p : ι → MvPolynomial (Fin n) K)
    (hp : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) :
    ∃ rs : List (MvPolynomial (Fin n) K), rs.length = n ∧
      (∀ r ∈ rs, r ∈ ProjectiveNullstellensatz.generated p) ∧ RingTheory.Sequence.IsRegular (MvPolynomial (Fin n) K) rs :=
  exists_regular_sequence_in_ideal (ProjectiveNullstellensatz.generated p)
    ((ProjectiveNullstellensatz.no_nonzero_root_iff_coordinate_powers p).mp hp)

end LeanCanny.Algebra.ProjectiveRegularSequence
