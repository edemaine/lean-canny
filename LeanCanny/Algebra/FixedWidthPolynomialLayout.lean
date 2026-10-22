/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialFP
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # Indexed coefficient sources in a native finite variable layout

A variable equivalence transports binary-rank exponent queries to the original
polynomial. A total-degree bound proves that every supported monomial is in the
finite enumeration. Coefficients are the actual collected native coefficients.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthPolynomial
open LeanCanny.Encoding
open RationalSubstitution.Indexed

variable {σ R : Type*} [Fintype σ] [CommSemiring R] {A : ℕ}

noncomputable def nativeExponent (f : σ ≃ Fin A) (W r : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => entry W r (f j).val)

/-- Repacking to a wider layout preserves the native exponent vector. -/
theorem nativeExponent_repack (f : σ ≃ Fin A) (W V : List Bool → ℕ)
    (target : List Bool → List Bool) (c : List Bool) (hW : W c ≤ V c) :
    nativeExponent f (V c) (Nat.fromBitsLE
      (FixedWidthQuery.repack (fun _ => A) W (fun _ => A) V target c)) =
      nativeExponent f (W c) (Nat.fromBitsLE (target c)) := by
  ext i
  simp only [nativeExponent, Finsupp.coe_equivFunOnFinite_symm]
  have he (width : ℕ) (bits : List Bool) (j : ℕ) :
      entry width (Nat.fromBitsLE bits) j =
        Nat.fromBitsLE ((bits.drop (j * width)).take width) := by
    rw [entry_eq_digit, BinaryNat.value_take, drop_value]
  rw [he, he]
  simpa only [FixedWidthQuery.coordinate, FixedWidthQuery.entry, (f i).isLt, ite_true] using
    FixedWidthQuery.coordinate_repack_of_width_le
      (fun _ => A) W (fun _ => A) V target c hW (f i).val (f i).isLt

theorem nativeExponent_map (f : σ ≃ Fin A) (W r : ℕ) :
    (nativeExponent f W r).mapDomain f = exponentVector A (entry W r) := by
  ext i
  simp only [Finsupp.mapDomain_equiv_apply, nativeExponent, exponentVector,
    Finsupp.coe_equivFunOnFinite_symm, Equiv.apply_symm_apply]

theorem coeff_rename_rank (f : σ ≃ Fin A) (p : MvPolynomial σ R) (W r : ℕ) :
    (MvPolynomial.rename f p).coeff (exponentVector A (entry W r)) = p.coeff (nativeExponent f W r) := by
  rw [← nativeExponent_map f W r, MvPolynomial.coeff_rename_mapDomain f f.injective]

theorem indexed_source_eq_rename (f : σ ≃ Fin A) (p : MvPolynomial σ R) (W D : ℕ)
    (hp : p.totalDegree ≤ D) (hW : D < 2 ^ W) :
    source A (count A W) (fun r => p.coeff (nativeExponent f W r)) (entry W) = MvPolynomial.rename f p := by
  have hc : (fun r => p.coeff (nativeExponent f W r)) =
      (fun r => (MvPolynomial.rename f p).coeff (exponentVector A (entry W r))) :=
    funext fun r => (coeff_rename_rank f p W r).symm
  rw [hc]
  apply indexed_source_eq
  intro m hm i
  have hi := MvPolynomial.monomial_le_degreeOf i hm
  exact (hi.trans ((MvPolynomial.degreeOf_le_totalDegree _ i).trans
    ((MvPolynomial.totalDegree_rename_le _ _).trans hp))).trans_lt hW

end LeanCanny.Algebra.FixedWidthPolynomial
