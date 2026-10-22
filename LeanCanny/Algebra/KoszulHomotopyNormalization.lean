/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedContractionMatrix

/-! # Square-zero normalization of the finite polynomial homotopy

The multidegree-dependent homotopy preserves each multidegree and squares
to zero. Together with the pure-power contraction identity, this proves
exactness of the homotopy maps themselves and injectivity in degree zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem wedge_square_zero (i : Fin n) (x : Total n R) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)
      (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) = 0 := by
  change ExteriorAlgebra.ι (Poly n R) (Pi.single i 1 : Fin n → Poly n R) *
    (ExteriorAlgebra.ι (Poly n R) (Pi.single i 1 : Fin n → Poly n R) * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem powerHomotopy_square_zero (d : Fin n → ℕ) (i : Fin n) (x : Total n R) :
    powerHomotopy (R := R) d i (powerHomotopy (R := R) d i x) = 0 := by
  rw [powerHomotopy_apply, powerHomotopy_apply, divide_wedge, wedge_square_zero]

theorem powerHomotopy_word_mem_component (d : Fin n → ℕ) (i : Fin n) {k : ℕ}
    (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    powerHomotopy (R := R) d i (monomialBlade (R := R) v m) ∈ component (R := R) d (m + wordExponent d v) := by
  rw [powerHomotopy_apply, divide_monomialBlade]
  split_ifs with ht
  · rw [wedge_monomialBlade]
    apply monomialBlade_mem_component
    rw [wordExponent_cons, ← add_assoc, tsub_add_cancel_of_le ht]
  · rw [map_zero]
    exact Submodule.zero_mem _

theorem powerHomotopy_component_mem (d : Fin n → ℕ) (i : Fin n) (t : Fin n →₀ ℕ)
    (x : Total n R) (hx : x ∈ component (R := R) d t) :
    powerHomotopy (R := R) d i x ∈ component (R := R) d t := by
  have hle : component (R := R) d t ≤ (component (R := R) d t).comap (powerHomotopy (R := R) d i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v, m, hm⟩, rfl⟩
    change powerHomotopy (R := R) d i (monomialBlade (R := R) v m) ∈ component (R := R) d t
    rw [← hm]
    exact powerHomotopy_word_mem_component d i v m
  exact hle hx

theorem levelHomotopy_component_mem (d : Fin n → ℕ) (t : Fin n →₀ ℕ) (ht : t.degree = Macaulay.level d)
    (x : Total n R) (hx : x ∈ component (R := R) d t) :
    levelHomotopy (R := R) d x ∈ component (R := R) d t := by
  rw [levelHomotopy_component d t ht x hx]
  exact powerHomotopy_component_mem d _ t x hx

theorem levelHomotopy_square_zero_word (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ)
    (ht : (m + wordExponent d v).degree = Macaulay.level d) :
    levelHomotopy (R := R) d (levelHomotopy (R := R) d (monomialBlade (R := R) v m)) = 0 := by
  have hx := monomialBlade_mem_component (R := R) d (m + wordExponent d v) v m rfl
  have hh := levelHomotopy_component_mem d _ ht _ hx
  rw [levelHomotopy_component d _ ht _ hh, levelHomotopy_word d v m ht, powerHomotopy_square_zero]

theorem levelHomotopy_square_zero (d : Fin n → ℕ) (W k : ℕ)
    (x : Total n R) (hx : x ∈ space (R := R) d (Macaulay.level d) W k) :
    levelHomotopy (R := R) d (levelHomotopy (R := R) d x) = 0 := by
  have hle : space (R := R) d (Macaulay.level d) W k ≤
      LinearMap.ker ((levelHomotopy (R := R) d).comp (levelHomotopy (R := R) d)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    have hg := (mem_indices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property
    have ht : (FixedWidthPolynomial.vector n W a.2.val + wordExponent d a.1).degree = Macaulay.level d := by
      rw [map_add, wordExponent_degree]
      exact hg
    exact levelHomotopy_square_zero_word d _ _ ht
  exact hle hx

theorem weightedHomotopy_comp (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (weightedHomotopy (R := R) d W hW (k + 1)).comp (weightedHomotopy (R := R) d W hW k) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact levelHomotopy_square_zero d W k x.val x.property

theorem homotopyMatrix_mul (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    homotopyMatrix (R := R) d W hW k * homotopyMatrix (R := R) d W hW (k + 1) = 0 := by
  unfold homotopyMatrix
  rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp, weightedHomotopy_comp, map_zero, Matrix.transpose_zero]

theorem weightedHomotopy_exact (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.ker (weightedHomotopy (R := R) d W hW (k + 1)) =
      LinearMap.range (weightedHomotopy (R := R) d W hW k) := by
  ext x
  constructor
  · intro hx
    refine ⟨differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k x, ?_⟩
    have h := LinearMap.congr_fun (weightedHomotopy_identity (R := R) d W hW k) x
    change differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1)
        (weightedHomotopy (R := R) d W hW (k + 1) x) +
      weightedHomotopy (R := R) d W hW k
        (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k x) = x at h
    rw [hx, map_zero, zero_add] at h
    exact h
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (weightedHomotopy_comp (R := R) d W hW k) y

theorem weightedHomotopy_zero_injective (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    Function.Injective (weightedHomotopy (R := R) d W hW 0) := by
  intro x y hxy
  have h := congrArg (differential (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW 0) hxy
  have hx := LinearMap.congr_fun (weightedHomotopy_zero_identity (R := R) d W hW) x
  have hy := LinearMap.congr_fun (weightedHomotopy_zero_identity (R := R) d W hW) y
  exact hx.symm.trans (h.trans hy)

end LeanCanny.Algebra.KoszulWeighted
