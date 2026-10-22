/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulLevelHomotopy

/-! # Contraction of the finite weighted pure-power Koszul complex

At the Macaulay level, the multidegree-dependent polynomial homotopy stays
inside the finite weighted pieces. Its homotopy identity proves exactness
in every positive exterior degree and surjectivity in degree zero, over
any commutative coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem powers_homogeneous (d : Fin n → ℕ) (i : Fin n) :
    (Macaulay.powers (R := R) d i).IsHomogeneous (d i) :=
  MvPolynomial.isHomogeneous_monomial 1 (Finsupp.degree_single i (d i))

theorem levelHomotopy_mem (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (x : Total n R) (hx : x ∈ space (R := R) d (Macaulay.level d) W k) :
    levelHomotopy (R := R) d x ∈ space (R := R) d (Macaulay.level d) W (k + 1) := by
  have hle : space (R := R) d (Macaulay.level d) W k ≤
      (space (R := R) d (Macaulay.level d) W (k + 1)).comap (levelHomotopy (R := R) d) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hg := (mem_indices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property
    have ht : (FixedWidthPolynomial.vector n W a.2.val + wordExponent d a.1).degree = Macaulay.level d := by
      rw [map_add, wordExponent_degree]
      exact hg
    change levelHomotopy (R := R) d (monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val)) ∈
      space (R := R) d (Macaulay.level d) W (k + 1)
    rw [levelHomotopy_word d _ _ ht, powerHomotopy_apply, divide_monomialBlade]
    split_ifs with hd
    · rw [wedge_monomialBlade]
      apply monomialBlade_mem d _ W (k + 1) hW
      have he := congrArg Finsupp.degree (tsub_add_cancel_of_le hd)
      simp only [map_add, Finsupp.degree_single] at he
      rw [wordWeight_cons]
      omega
    · rw [map_zero]
      exact Submodule.zero_mem _
  exact hle hx

theorem levelHomotopy_identity (d : Fin n → ℕ) (W k : ℕ)
    (x : Total n R) (hx : x ∈ space (R := R) d (Macaulay.level d) W k) :
    KoszulExterior.differential (Macaulay.powers (R := R) d) (levelHomotopy (R := R) d x) +
      levelHomotopy (R := R) d (KoszulExterior.differential (Macaulay.powers (R := R) d) x) = x := by
  let D := (KoszulExterior.differential (Macaulay.powers (R := R) d)).restrictScalars R
  let H := levelHomotopy (R := R) d
  have hle : space (R := R) d (Macaulay.level d) W k ≤
      LinearMap.ker ((D.comp H + H.comp D) - LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hg := (mem_indices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property
    have ht : (FixedWidthPolynomial.vector n W a.2.val + wordExponent d a.1).degree = Macaulay.level d := by
      rw [map_add, wordExponent_degree]
      exact hg
    change KoszulExterior.differential (Macaulay.powers (R := R) d)
        (levelHomotopy (R := R) d (monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val))) +
      levelHomotopy (R := R) d (KoszulExterior.differential (Macaulay.powers (R := R) d)
        (monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val))) -
      monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val) = 0
    exact sub_eq_zero.mpr (levelHomotopy_identity_word d _ _ ht)
  exact sub_eq_zero.mp (hle hx)

noncomputable def weightedHomotopy (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    space (R := R) d (Macaulay.level d) W k →ₗ[R] space (R := R) d (Macaulay.level d) W (k + 1) :=
  ((levelHomotopy (R := R) d).comp (space (R := R) d (Macaulay.level d) W k).subtype).codRestrict _
    (fun x => levelHomotopy_mem d W k hW x.val x.property)

theorem weightedHomotopy_identity (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)).comp
        (weightedHomotopy d W hW (k + 1)) +
      (weightedHomotopy d W hW k).comp
        (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact levelHomotopy_identity d W (k + 1) x.val x.property

theorem weightedHomotopy_zero_identity (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW 0).comp
      (weightedHomotopy d W hW 0) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := levelHomotopy_identity d W 0 x.val x.property
  rw [differential_degree_zero _ _ _ _ _ x.property, map_zero, add_zero] at h
  exact h

theorem powers_weighted_kernel_iff (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (x : Total n R) (hx : x ∈ space (R := R) d (Macaulay.level d) W k) :
    KoszulExterior.differential (Macaulay.powers (R := R) d) x = 0 ↔
      ∃ y ∈ space (R := R) d (Macaulay.level d) W (k + 1),
        KoszulExterior.differential (Macaulay.powers (R := R) d) y = x := by
  constructor
  · intro hz
    refine ⟨levelHomotopy (R := R) d x, levelHomotopy_mem d W k hW x hx, ?_⟩
    have h := levelHomotopy_identity d W k x hx
    simpa only [hz, map_zero, add_zero] using h
  · rintro ⟨y, _, rfl⟩
    exact KoszulExterior.differential_square_zero _ _

theorem powers_weighted_exact (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.ker (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k) =
      LinearMap.range (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)) := by
  ext x
  constructor
  · intro hx
    have hz : KoszulExterior.differential (Macaulay.powers (R := R) d) x.val = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy, he⟩ := (powers_weighted_kernel_iff d W (k + 1) hW x.val x.property).mp hz
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact KoszulExterior.differential_square_zero _ _

theorem powers_weighted_zero_surjective (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    Function.Surjective (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW 0) := by
  intro x
  refine ⟨weightedHomotopy d W hW 0 x, ?_⟩
  exact LinearMap.congr_fun (weightedHomotopy_zero_identity d W hW) x

end LeanCanny.Algebra.KoszulWeighted
