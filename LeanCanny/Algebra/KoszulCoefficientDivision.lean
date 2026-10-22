/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedBasis
public import LeanCanny.Algebra.KoszulWeightedComplex

/-! # Monomial division on exterior coefficients

Division by a monomial discards coefficient terms which it does not divide.
The resulting coefficient-ring linear operator commutes with insertion of
coordinate exterior generators. Multiplication by the divisor followed by
division is the identity.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def divide (t : Fin n →₀ ℕ) : Total n R →ₗ[R] Total n R :=
  (ambientBasis (R := R)).constr R
    (fun a => if t ≤ a.1 then ambientBasis (R := R) (a.1 - t, a.2) else 0)

theorem divide_ambientBasis (t m : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    divide (R := R) t (ambientBasis (R := R) (m, s)) =
      if t ≤ m then ambientBasis (R := R) (m - t, s) else 0 :=
  Module.Basis.constr_basis _ _ _ _

theorem monomialBlade_sorted {k : ℕ} (v : Fin k → Fin n) (hv : Function.Injective v) (m : Fin n →₀ ℕ) :
    monomialBlade (R := R) (v ∘ sortPermutation v hv) m =
      ambientBasis (R := R) (m, Finset.univ.image v) := by
  rw [sortPermutation_order, ambientBasis_apply,
    exteriorBasis_as_blade _ (image_card_of_injective v hv)]
  rfl

theorem divide_monomialBlade (t m : Fin n →₀ ℕ) {k : ℕ} (v : Fin k → Fin n) :
    divide (R := R) t (monomialBlade (R := R) v m) =
      if t ≤ m then monomialBlade (R := R) v (m - t) else 0 := by
  by_cases hv : Function.Injective v
  · have hu : IsUnit ((sortPermutation v hv).sign : R) :=
      IsUnit.map (Int.castRingHom R) (sortPermutation v hv).sign.isUnit
    apply hu.smul_left_cancel.mp
    rw [← map_smul, ← monomialBlade_perm, monomialBlade_sorted, divide_ambientBasis]
    split_ifs with h
    · rw [← monomialBlade_perm, monomialBlade_sorted]
    · rw [smul_zero]
  · simp only [monomialBlade, blade_eq_zero_of_not_injective v hv, smul_zero, map_zero, ite_self]

theorem wedge_monomialBlade (i : Fin n) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) :
    KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (monomialBlade (R := R) v m) =
      monomialBlade (R := R) (Fin.cons i v) m := by
  rw [monomialBlade, map_smul, monomialBlade, blade_cons]
  rfl

theorem divide_wedge (t : Fin n →₀ ℕ) (i : Fin n) (x : Total n R) :
    divide (R := R) t (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) =
      KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (divide (R := R) t x) := by
  have h : (divide (R := R) t).comp
      ((KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)).restrictScalars R) =
      ((KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)).restrictScalars R).comp (divide (R := R) t) := by
    apply (ambientBasis (R := R)).ext
    rintro ⟨m, s⟩
    rw [ambientBasis_apply, exteriorBasis_as_blade s rfl]
    change divide (R := R) t (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)
      (monomialBlade (R := R) (s.orderEmbOfFin rfl) m)) =
        KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R)
          (divide (R := R) t (monomialBlade (R := R) (s.orderEmbOfFin rfl) m))
    rw [wedge_monomialBlade, divide_monomialBlade, divide_monomialBlade]
    split_ifs
    · exact (wedge_monomialBlade _ _ _).symm
    · exact (map_zero _).symm
  exact LinearMap.congr_fun h x

theorem monomial_smul_monomialBlade (t m : Fin n →₀ ℕ) {k : ℕ} (v : Fin k → Fin n) :
    MvPolynomial.monomial t (1 : R) • monomialBlade (R := R) v m = monomialBlade (R := R) v (t + m) := by
  rw [monomialBlade, smul_smul, MvPolynomial.monomial_mul_monomial, one_mul]
  rfl

theorem divide_monomial_smul (t : Fin n →₀ ℕ) (x : Total n R) :
    divide (R := R) t (MvPolynomial.monomial t (1 : R) • x) = x := by
  have h : (divide (R := R) t).comp
      (((Algebra.lsmul (Poly n R) (Poly n R) (Total n R)) (MvPolynomial.monomial t (1 : R))).restrictScalars R) =
      LinearMap.id := by
    apply (ambientBasis (R := R)).ext
    rintro ⟨m, s⟩
    rw [ambientBasis_apply, exteriorBasis_as_blade s rfl]
    change divide (R := R) t (MvPolynomial.monomial t (1 : R) •
      monomialBlade (R := R) (s.orderEmbOfFin rfl) m) = monomialBlade (R := R) (s.orderEmbOfFin rfl) m
    rw [monomial_smul_monomialBlade, divide_monomialBlade, ite_eq_left le_self_add, add_tsub_cancel_left]
  exact LinearMap.congr_fun h x

theorem divide_monomial_smul_of_le (t m a : Fin n →₀ ℕ) (ht : t ≤ m) {k : ℕ} (v : Fin k → Fin n) :
    divide (R := R) t (MvPolynomial.monomial a (1 : R) • monomialBlade (R := R) v m) =
      MvPolynomial.monomial a (1 : R) • divide (R := R) t (monomialBlade (R := R) v m) := by
  have hta : t ≤ a + m := ht.trans le_add_self
  rw [monomial_smul_monomialBlade, divide_monomialBlade, divide_monomialBlade, ite_eq_left hta, ite_eq_left ht,
    monomial_smul_monomialBlade, add_tsub_assoc_of_le ht]

end LeanCanny.Algebra.KoszulWeighted
