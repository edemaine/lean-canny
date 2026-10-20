/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCoefficientMap
public import LeanCanny.Algebra.KoszulLinearInput
public import LeanCanny.Algebra.KoszulWeightedContractionMatrix

/-! # Coefficient maps and linear pencils of canonical Koszul matrices

The canonical differential and pure-power homotopy matrices commute with
coefficient homomorphisms. The differential matrix depends linearly on its
input system, including scalar polynomial pencils.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem canonicalMatrix_congr {p q : Fin n → Poly n R} (he : p = q) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hq : ∀ i, (q i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    canonicalMatrix p d L W hp hW k = canonicalMatrix q d L W hq hW k := by
  subst q
  rfl

theorem coefficientMap_canonicalGenerator (φ : R →+* S) (d : Fin n → ℕ) (L W k : ℕ)
    (a : CanonicalIndex d L W k) :
    coefficientMap φ (canonicalGenerator (R := R) d L W k a) = canonicalGenerator (R := S) d L W k a :=
  coefficientMap_ambientBasis φ _

theorem canonicalMatrix_map (φ : R →+* S) (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    canonicalMatrix (fun i => (p i).map φ) d L W (fun i => (hp i).map φ) hW k =
      (canonicalMatrix p d L W hp hW k).map φ := by
  ext a b
  change canonicalMatrix (fun i => (p i).map φ) d L W _ hW k a b = φ (canonicalMatrix p d L W hp hW k a b)
  rw [canonicalMatrix_apply, canonicalMatrix_apply]
  have h := coefficientMap_differential φ p (canonicalGenerator (R := R) d L W (k + 1) a)
  rw [coefficientMap_canonicalGenerator] at h
  rw [← h, coefficientMap_repr, MvPolynomial.coeff_map]

theorem canonicalMatrix_sub_smul (p q : Fin n → Poly n R) (a : R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hq : ∀ i, (q i).IsHomogeneous (d i))
    (hsub : ∀ i, (p i - MvPolynomial.C a * q i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    canonicalMatrix (fun i => p i - MvPolynomial.C a * q i) d L W hsub hW k =
      canonicalMatrix p d L W hp hW k - a • canonicalMatrix q d L W hq hW k := by
  ext u v
  simp only [Matrix.sub_apply, Matrix.smul_apply, canonicalMatrix_apply,
    KoszulExterior.differential_sub_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
    MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul]

theorem coefficientMap_powerHomotopy_word (φ : R →+* S) (d : Fin n → ℕ) (i : Fin n)
    {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    coefficientMap φ (powerHomotopy (R := R) d i (monomialBlade (R := R) v m)) =
      powerHomotopy (R := S) d i (monomialBlade (R := S) v m) := by
  rw [powerHomotopy_apply, coefficientMap_wedge, divide_monomialBlade, powerHomotopy_apply, divide_monomialBlade]
  split_ifs <;> simp only [coefficientMap_monomialBlade, map_zero]

theorem coefficientMap_levelHomotopy_word (φ : R →+* S) (d : Fin n → ℕ) {k : ℕ}
    (v : Fin k → Fin n) (m : Fin n →₀ ℕ) (ht : (m + wordExponent d v).degree = Macaulay.level d) :
    coefficientMap φ (levelHomotopy (R := R) d (monomialBlade (R := R) v m)) =
      levelHomotopy (R := S) d (monomialBlade (R := S) v m) := by
  rw [levelHomotopy_word d v m ht, levelHomotopy_word d v m ht]
  exact coefficientMap_powerHomotopy_word φ d _ v m

theorem coefficientMap_levelHomotopy_generator (φ : R →+* S) (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) :
    coefficientMap φ (levelHomotopy (R := R) d (canonicalGenerator (R := R) d (Macaulay.level d) W k a)) =
      levelHomotopy (R := S) d (canonicalGenerator (R := S) d (Macaulay.level d) W k a) := by
  have ha := (mem_canonicalIndices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property
  have ht : (FixedWidthPolynomial.vector n W a.2.val + wordExponent d (a.1.orderEmbOfFin ha.1)).degree =
      Macaulay.level d := by
    rw [map_add, wordExponent_degree, wordWeight_ordered]
    exact ha.2
  rw [canonicalGenerator_apply, canonicalGenerator_apply, exteriorBasis_as_blade a.1 ha.1,
    exteriorBasis_as_blade a.1 ha.1]
  exact coefficientMap_levelHomotopy_word φ d _ _ ht

theorem homotopyMatrix_apply (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) (b : CanonicalIndex d (Macaulay.level d) W (k + 1)) :
    homotopyMatrix (R := R) d W hW k a b =
      ((exteriorBasis (R := R)).repr
        (levelHomotopy (R := R) d (canonicalGenerator (R := R) d (Macaulay.level d) W k a)) b.1).coeff
          (FixedWidthPolynomial.vector n W b.2.val) := by
  rw [homotopyMatrix, Matrix.transpose_apply, LinearMap.toMatrix_apply, canonicalBasis_repr_coeff]
  change ((exteriorBasis (R := R)).repr
    (levelHomotopy (R := R) d (canonicalBasis (R := R) d (Macaulay.level d) W k a : Total n R)) b.1).coeff _ = _
  rw [canonicalBasis_apply]

theorem homotopyMatrix_map (φ : R →+* S) (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    homotopyMatrix (R := S) d W hW k = (homotopyMatrix (R := R) d W hW k).map φ := by
  ext a b
  change homotopyMatrix (R := S) d W hW k a b = φ (homotopyMatrix (R := R) d W hW k a b)
  rw [homotopyMatrix_apply, homotopyMatrix_apply,
    ← coefficientMap_levelHomotopy_generator φ d W k a, coefficientMap_repr, MvPolynomial.coeff_map]

end LeanCanny.Algebra.KoszulWeighted
