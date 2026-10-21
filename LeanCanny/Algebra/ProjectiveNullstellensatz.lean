/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Ideal

/-! # Ideal certificates for the absence of projective common roots

Over an algebraically closed field, having no nonzero common root is
equivalent to containing a power of every coordinate in the generated
ideal. Equivalently, a power of the variable ideal is contained in that
ideal, or every homogeneous form of some degree belongs to it.
These are qualitative certificates; no Macaulay degree bound is asserted.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectiveNullstellensatz
open scoped Classical
variable {σ ι R : Type*} [CommRing R]

noncomputable def generated (p : ι → MvPolynomial σ R) : Ideal (MvPolynomial σ R) := Ideal.span (Set.range p)

theorem eval_eq_zero_of_mem (p : ι → MvPolynomial σ R) (x : σ → R)
    (hx : ∀ i, MvPolynomial.eval x (p i) = 0) {f : MvPolynomial σ R} (hf : f ∈ generated p) :
    MvPolynomial.eval x f = 0 := by
  have he : generated p ≤ RingHom.ker (MvPolynomial.eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hx i
  exact he hf

theorem coordinate_powers_imply_no_nonzero_root [IsDomain R] (p : ι → MvPolynomial σ R)
    (hp : ∀ j : σ, ∃ N : ℕ, MvPolynomial.X j ^ N ∈ generated p)
    (x : σ → R) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) : x = 0 := by
  funext j
  obtain ⟨N, hN⟩ := hp j
  have he := eval_eq_zero_of_mem p x hx hN
  simp only [map_pow, MvPolynomial.eval_X] at he
  exact eq_zero_of_pow_eq_zero he

variable {K : Type*} [Field K] [IsAlgClosed K] [Finite σ]

omit [IsAlgClosed K] [Finite σ] in
theorem zeroLocus_generated (p : ι → MvPolynomial σ K) :
    MvPolynomial.zeroLocus K (generated p) = {x | ∀ i, MvPolynomial.eval x (p i) = 0} := by
  rw [generated, MvPolynomial.zeroLocus_span]
  simp only [Set.forall_mem_range, MvPolynomial.aeval_eq_eval]

theorem no_nonzero_root_iff_coordinate_powers (p : ι → MvPolynomial σ K) :
    (∀ x : σ → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) ↔
      ∀ j : σ, ∃ N : ℕ, MvPolynomial.X j ^ N ∈ generated p := by
  constructor
  · intro h j
    apply Ideal.mem_radical_iff.mp
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have hz := h x (by simpa only [zeroLocus_generated, Set.mem_ofPred_eq] using hx)
    rw [hz]
    simp
  · exact coordinate_powers_imply_no_nonzero_root p

theorem no_nonzero_root_iff_variable_ideal_pow (p : ι → MvPolynomial σ K) :
    (∀ x : σ → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) ↔
      ∃ N : ℕ, MvPolynomial.idealOfVars σ K ^ N ≤ generated p := by
  constructor
  · intro h
    have hc := (no_nonzero_root_iff_coordinate_powers p).mp h
    have hr : MvPolynomial.idealOfVars σ K ≤ (generated p).radical := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_radical_iff.mpr (hc j)
    exact Ideal.exists_pow_le_of_le_radical_of_fg hr (MvPolynomial.idealOfVars_fg σ K)
  · rintro ⟨N, hN⟩
    apply (no_nonzero_root_iff_coordinate_powers p).mpr
    intro j
    have hj : (MvPolynomial.X j : MvPolynomial σ K) ∈ MvPolynomial.idealOfVars σ K := Ideal.subset_span ⟨j, rfl⟩
    exact ⟨N, hN (Ideal.pow_mem_pow hj N)⟩

omit [IsAlgClosed K] [Finite σ] in
theorem homogeneous_mem_of_variable_ideal_pow_le (p : ι → MvPolynomial σ K) (N t : ℕ)
    (hN : MvPolynomial.idealOfVars σ K ^ N ≤ generated p) (ht : N ≤ t)
    (f : MvPolynomial σ K) (hf : f.IsHomogeneous t) : f ∈ generated p := by
  apply hN
  rw [MvPolynomial.mem_pow_idealOfVars_iff]
  intro m hm
  have he : m.degree = t := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hm) (hf.coeff_eq_zero hn)
  exact he ▸ ht

theorem no_nonzero_root_iff_homogeneous_membership (p : ι → MvPolynomial σ K) :
    (∀ x : σ → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) ↔
      ∃ N : ℕ, ∀ f : MvPolynomial σ K, f.IsHomogeneous N → f ∈ generated p := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (no_nonzero_root_iff_variable_ideal_pow p).mp h
    exact ⟨N, fun f hf => homogeneous_mem_of_variable_ideal_pow_le p N N hN le_rfl f hf⟩
  · rintro ⟨N, hN⟩
    apply (no_nonzero_root_iff_coordinate_powers p).mpr
    intro j
    exact ⟨N, hN _ (by simpa only [one_mul] using (MvPolynomial.isHomogeneous_X (R := K) j).pow N)⟩

end LeanCanny.Algebra.ProjectiveNullstellensatz
