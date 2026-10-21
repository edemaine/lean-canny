/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveRegularSequence
public import Mathlib.RingTheory.Depth.Rees

/-! # Ext vanishing for ideals without projective common roots

Positive homogeneous inputs generate a proper ideal. If their only common
root over an algebraically closed field is zero, that ideal contains an
ambient regular sequence of length equal to the number of variables.
Rees' theorem gives Ext vanishing below that length for every finite
module supported on the input ideal's zero locus.
-/

@[expose] public section

universe u

namespace LeanCanny.Algebra.ProjectiveDepth
open scoped Classical

theorem generated_ne_top_of_positive_homogeneous {σ ι R : Type*} [CommRing R] [Nontrivial R]
    (p : ι → MvPolynomial σ R) (d : ι → ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) :
    ProjectiveNullstellensatz.generated p ≠ ⊤ := by
  have hroot : ∀ i, MvPolynomial.eval (0 : σ → R) (p i) = 0 := by
    intro i
    rw [MvPolynomial.eval_zero]
    change (p i).coeff 0 = 0
    exact (hp i).coeff_eq_zero (by simpa only [map_zero] using ne_of_lt (hd i))
  intro he
  have hmem : (1 : MvPolynomial σ R) ∈ ProjectiveNullstellensatz.generated p := by rw [he]; exact Submodule.mem_top
  have hz := ProjectiveNullstellensatz.eval_eq_zero_of_mem p 0 hroot hmem
  rw [map_one] at hz
  exact one_ne_zero hz

variable {n m : ℕ} {K : Type u} [Field K] [IsAlgClosed K]

theorem subsingleton_ext_of_no_nonzero_root (p : Fin m → MvPolynomial (Fin n) K) (d : Fin m → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0)
    (N : ModuleCat.{u} (MvPolynomial (Fin n) K)) [Module.Finite (MvPolynomial (Fin n) K) N]
    (hN : Module.support (MvPolynomial (Fin n) K) N ⊆ PrimeSpectrum.zeroLocus (ProjectiveNullstellensatz.generated p))
    (i : ℕ) (hi : i < n) :
    Subsingleton (CategoryTheory.Abelian.Ext N (ModuleCat.of (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)) i) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := ProjectiveRegularSequence.exists_regular_sequence_of_no_nonzero_root p hroot
  have hproper := generated_ne_top_of_positive_homogeneous p d hp hd
  have hsmul : ProjectiveNullstellensatz.generated p •
      (⊤ : Submodule (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)) < ⊤ := by
    change (ProjectiveNullstellensatz.generated p * ⊤ : Ideal (MvPolynomial (Fin n) K)) < ⊤
    rw [Ideal.mul_top]
    exact lt_top_iff_ne_top.mpr hproper
  exact ModuleCat.subsingleton_ext_of_exists_isRegular (ProjectiveNullstellensatz.generated p) N hN
    (ModuleCat.of (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)) hsmul rs hmem hreg i (by rwa [hlen])

theorem subsingleton_ext_quotient_of_no_nonzero_root (p : Fin m → MvPolynomial (Fin n) K) (d : Fin m → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0)
    (i : ℕ) (hi : i < n) :
    Subsingleton (CategoryTheory.Abelian.Ext
      (ModuleCat.of (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K ⧸ ProjectiveNullstellensatz.generated p))
      (ModuleCat.of (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) K)) i) := by
  apply subsingleton_ext_of_no_nonzero_root p d hp hd hroot _ _ i hi
  rw [Module.support_of_algebra]
  change PrimeSpectrum.zeroLocus ((RingHom.ker (Ideal.Quotient.mk (ProjectiveNullstellensatz.generated p))) :
    Set (MvPolynomial (Fin n) K)) ⊆ _
  rw [Ideal.mk_ker]

end LeanCanny.Algebra.ProjectiveDepth
