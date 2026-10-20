/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedSpace
public import LeanCanny.Algebra.KoszulComplex

/-! # The finite weighted Koszul chain complex

Homogeneous input polynomials preserve the total weight of a monomial
exterior word under the Koszul differential. Restriction to the finite
weighted pieces gives a chain complex of finite coefficient modules.
Higher exactness is not asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem differential_monomialBlade_zero (p : Fin n → Poly n R) (v : Fin 0 → Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.differential p (monomialBlade (R := R) v m) = 0 := by
  have hz : KoszulExterior.differential p (1 : Total n R) = 0 :=
    CliffordAlgebra.contractLeft_one _ (KoszulExterior.linearForm p)
  rw [monomialBlade, blade_zero, map_smul, hz, smul_zero]

theorem differential_monomialBlade_succ (p : Fin n → Poly n R) {k : ℕ}
    (v : Fin (k + 1) → Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.differential p (monomialBlade (R := R) v m) =
      (MvPolynomial.monomial m (1 : R) * p (v 0)) • blade (R := R) (Matrix.vecTail v) -
        KoszulExterior.wedge (Pi.single (v 0) 1 : Fin n → Poly n R)
          (KoszulExterior.differential p (monomialBlade (R := R) (Matrix.vecTail v) m)) := by
  simp only [monomialBlade, map_smul, blade_succ, KoszulExterior.differential_ι_mul,
    KoszulExterior.linearForm_single, smul_sub, smul_smul]
  rfl

theorem differential_mem (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W k : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (x : Total n R)
    (hx : x ∈ space (R := R) d L W (k + 1)) :
    KoszulExterior.differential p x ∈ space (R := R) d L W k := by
  induction k generalizing L x with
  | zero =>
    have hle : space (R := R) d L W 1 ≤ (space (R := R) d L W 0).comap
        ((KoszulExterior.differential p).restrictScalars R) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change KoszulExterior.differential p (monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val)) ∈
        space (R := R) d L W 0
      rw [differential_monomialBlade_succ, differential_monomialBlade_zero, map_zero, sub_zero]
      have hg := (mem_indices d L W 1 a.1 a.2.val).mp a.2.property
      rw [wordWeight_succ] at hg
      exact homogeneous_smul_blade_mem d L W 0 _ hW _
        ((MvPolynomial.isHomogeneous_monomial (1 : R) rfl).mul (hp (a.1 0))) (Matrix.vecTail a.1) (by omega)
    exact hle hx
  | succ k ih =>
    have hle : space (R := R) d L W (k + 1 + 1) ≤ (space (R := R) d L W (k + 1)).comap
        ((KoszulExterior.differential p).restrictScalars R) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change KoszulExterior.differential p (monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val)) ∈
        space (R := R) d L W (k + 1)
      rw [differential_monomialBlade_succ]
      apply Submodule.sub_mem
      · have hg := (mem_indices d L W (k + 1 + 1) a.1 a.2.val).mp a.2.property
        rw [wordWeight_succ] at hg
        exact homogeneous_smul_blade_mem d L W (k + 1) _ hW _
          ((MvPolynomial.isHomogeneous_monomial (1 : R) rfl).mul (hp (a.1 0))) (Matrix.vecTail a.1) (by omega)
      · have hg := (mem_indices d L W (k + 1 + 1) a.1 a.2.val).mp a.2.property
        rw [wordWeight_succ] at hg
        have hWt : L - d (a.1 0) < 2 ^ W := (Nat.sub_le _ _).trans_lt hW
        have ht : monomialBlade (R := R) (Matrix.vecTail a.1) (FixedWidthPolynomial.vector n W a.2.val) ∈
            space (R := R) d (L - d (a.1 0)) W (k + 1) :=
          monomialBlade_mem d _ W (k + 1) hWt _ _ (by omega)
        have hd := ih _ hWt _ ht
        have hw := wedge_mem d (L - d (a.1 0)) W k (a.1 0) _ hd
        have he : L - d (a.1 0) + d (a.1 0) = L := by omega
        simpa only [he] using hw
    exact hle hx

theorem differential_degree_zero (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (x : Total n R) (hx : x ∈ space (R := R) d L W 0) : KoszulExterior.differential p x = 0 :=
  KoszulExterior.differential_degree_zero p x (space_le_exteriorGrade d L W 0 hx)

noncomputable def differential (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    space (R := R) d L W (k + 1) →ₗ[R] space (R := R) d L W k :=
  (((KoszulExterior.differential p).restrictScalars R).comp (space (R := R) d L W (k + 1)).subtype).codRestrict _
    (fun x => differential_mem p d L W k hp hW x.val x.property)

theorem differential_comp (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    (differential p d L W hp hW k).comp (differential p d L W hp hW (k + 1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact KoszulExterior.differential_square_zero p x.val

noncomputable def complex (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of R (space (R := R) d L W k))
    (fun k => ModuleCat.ofHom (differential p d L W hp hW k)) (fun k => by
      apply ModuleCat.hom_ext
      exact differential_comp p d L W hp hW k)

end LeanCanny.Algebra.KoszulWeighted
