/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientUniformIntegralPrefixRows
public import LeanCanny.Algebra.CanonicalIntegralScalarAppend

/-! # Scalar append rows over a generic coefficient base

The old physical index and scalar slots are retained. The new row is the
actual padded equation with the native layout and global power schedule.
-/

@[expose] public section
namespace LeanCanny.Algebra
open MvPolynomial
open scoped Classical

namespace CoordinatePowerSubstitution
variable {R T σ : Type*} [CommRing R] [CommRing T]

theorem map_substitute (φ : R →+* T) (w : σ → ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.map φ (substitute w p) = substitute w (MvPolynomial.map φ p) := by
  simpa only [substitute, map_pow, MvPolynomial.map_X] using
    MvPolynomial.map_bind₁ φ (fun i => (X i : MvPolynomial σ R) ^ w i) p

end CoordinatePowerSubstitution

namespace MonicParameterRows
variable {R T σ : Type*} [CommRing R] [CommRing T]

theorem map_row (φ : R →+* T) (p : Polynomial (MvPolynomial σ R))
    (d : ℕ) (w : σ → ℕ) (W : ℕ) :
    MvPolynomial.map φ (row p d w W) = row (p.map (MvPolynomial.map φ)) d w W := by
  simp only [row, lower, map_add, map_pow, MvPolynomial.map_X, map_sum, map_mul,
    MvPolynomial.map_rename, CoordinatePowerSubstitution.map_substitute,
    coefficient, Polynomial.coeff_map]

end MonicParameterRows

namespace CoefficientCanonicalScalarAppend
open UniformIntegralPowerSchedule CoefficientUniformIntegralPrefixRows
set_option backward.isDefEq.respectTransparency false
variable {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {m N : ℕ}

abbrev layout := @CanonicalIntegralScalarAppend.layout
abbrev degrees := @CanonicalIntegralScalarAppend.degrees

noncomputable def rows (S : ℕ) (q : ι → MvPolynomial ι R) (f : Fin m → ι)
    (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A) (d : ℕ) :
    (ι ⊕ Unit) → MvPolynomial (ι ⊕ Unit) R :=
  TriangularPolynomialSystem.append q (fun _ => rename (layout f) (MonicParameterRows.row
    (equation b p d) N (weights S N m) (birth S N m)))

theorem newrows_map {T B : Type*} [CommRing T] [CommRing B] [Algebra T B]
    {φ : R →+* T} {ψ : A →+* B} {b : CoefficientCoordinateBasis R A m N}
    {c : CoefficientCoordinateBasis T B m N} (H : CoefficientCoordinateBasis.Specializes φ ψ b c)
    (S : ℕ) (q : ι → MvPolynomial ι R) (q' : ι → MvPolynomial ι T)
    (HQ : ∀ i, MvPolynomial.map φ (q i) = q' i) (f : Fin m → ι) (p : Polynomial A) (d : ℕ) :
    (fun i => MvPolynomial.map φ (rows S q f b p d i)) = rows S q' f c (p.map ψ) d := by
  funext i
  cases i with
  | inl j => simp only [rows, TriangularPolynomialSystem.append, Sum.elim_inl, MvPolynomial.map_rename, HQ]
  | inr u =>
    simp only [rows, TriangularPolynomialSystem.append, Sum.elim_inr, MvPolynomial.map_rename,
      MonicParameterRows.map_row, equation_map H]

theorem row_degree (S : ℕ) (hm : m ≤ S) (hN : 0 < N)
    (q : ι → MvPolynomial ι R) (e : ι → ℕ) (hq : ∀ i, (q i).totalDegree ≤ e i)
    (f : Fin m → ι) (b : CoefficientCoordinateBasis R A m N) (p : Polynomial A) (d : ℕ)
    (j : ι ⊕ Unit) : (rows S q f b p d j).totalDegree ≤ degrees S N m e j := by
  cases j with
  | inl i => exact (totalDegree_rename_le _ _).trans (hq i)
  | inr u =>
    apply (totalDegree_rename_le _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le ?_ (CoefficientUniformIntegralPrefixRows.scalar_lower_degree S hm hN b p d).le
    simpa only [Nat.one_mul] using
      ((isHomogeneous_X (R := R) (Sum.inr () : Fin m ⊕ Unit)).pow (N * birth S N m)).totalDegree_le

theorem rows_ofIntegral (S : ℕ) (q : ι → MvPolynomial ι ℤ) (f : Fin m → ι)
    (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    rows S q f (CoefficientCoordinateBasis.ofIntegral b) p d =
      CanonicalIntegralScalarAppend.rows S q f b p d := rfl

end CoefficientCanonicalScalarAppend
end LeanCanny.Algebra
