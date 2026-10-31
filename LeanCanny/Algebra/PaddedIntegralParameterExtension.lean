/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralNormalization
public import LeanCanny.Algebra.IntegralCoordinateBasis
public import LeanCanny.Algebra.IntegralCoordinatePolynomial

/-! # Uniform-rank scalar extensions with bounded height numerators

Every monic scalar extension has the same rank N. Its exact height is a
quotient with a nonzero integer denominator. The numerator has a canonical
polynomial representative whose exponents are all below N, regardless of
the old algebra rank, nonreduced branches, or coefficient sizes.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m N : ℕ}

noncomputable abbrev Extension (p : Polynomial A) (d N : ℕ) :=
  AdjoinRoot (PaddedIntegralNormalization.polynomial p d N)

theorem nontrivial (p : Polynomial A) (d N : ℕ) (hN : 0 < N) : Nontrivial (Extension p d N) :=
  PaddedIntegralNormalization.extension_nontrivial p d N hN

noncomputable def coordinateBasis (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    IntegralCoordinateBasis (Extension p d N) (m + 1) N :=
  b.step (PaddedIntegralNormalization.polynomial p d N)
    (PaddedIntegralNormalization.monic p d N) (PaddedIntegralNormalization.natDegree p d N)

noncomputable def equation (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    Polynomial (MvPolynomial (Fin m) ℤ) := b.polynomial (PaddedIntegralNormalization.polynomial p d N)

theorem equation_monic (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) (hN : 0 < N) :
    (equation b p d).Monic ∧ (equation b p d).natDegree = N := by
  have H := b.polynomial_monic hN _ (PaddedIntegralNormalization.monic p d N)
  simpa only [equation, PaddedIntegralNormalization.natDegree] using H

omit [Nontrivial A] in
theorem equation_coefficient_degree (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d i : ℕ) :
    ((equation b p d).coeff i).totalDegree ≤ m * (N - 1) := b.polynomial_coefficient_degree _ i

variable {K : Type*} [Field K]

omit [Nontrivial A] in
theorem equation_root (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hdN : d ≤ N) (φ : A →ₐ[ℤ] K) (t : K) (hd : (p.map φ.toRingHom).natDegree = d)
    (hpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    (equation b p d).eval₂ (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom
      (φ (p.coeff d) * t) = 0 := by
  rw [equation, b.polynomial_eval]
  exact PaddedIntegralNormalization.scaled_root p d N hdN φ.toRingHom hd hpos t ht

noncomputable def evaluate (p : Polynomial A) (d N : ℕ) (hdN : d ≤ N) (φ : A →ₐ[ℤ] K) (t : K)
    (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    Extension p d N →ₐ[ℤ] K :=
  AdjoinRoot.liftAlgHom _ φ (φ (p.coeff d) * t)
    (PaddedIntegralNormalization.scaled_root p d N hdN φ.toRingHom hd hpos t ht)

omit [Nontrivial A] in
theorem evaluate_of (p : Polynomial A) (d N : ℕ) hdN (φ : A →ₐ[ℤ] K) (t : K) hd hpos ht (a : A) :
    evaluate p d N hdN φ t hd hpos ht (AdjoinRoot.of _ a) = φ a :=
  AdjoinRoot.liftAlgHom_of _ φ _ _ a

omit [Nontrivial A] in
theorem evaluate_root (p : Polynomial A) (d N : ℕ) hdN (φ : A →ₐ[ℤ] K) (t : K) hd hpos ht :
    evaluate p d N hdN φ t hd hpos ht (AdjoinRoot.root _) = φ (p.coeff d) * t :=
  AdjoinRoot.liftAlgHom_root _ φ _ _

noncomputable def denominator (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) : ℤ :=
  IntegralParameterInverse.denominator (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly

noncomputable def numerator (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) : Extension p d N :=
  AdjoinRoot.root _ * AdjoinRoot.of _
    (Polynomial.aeval (p.coeff d)
      (IntegralParameterInverse.inverse (Algebra.leftMulMatrix b.basis (p.coeff d)).charpoly))

omit [Nontrivial A] in
theorem denominator_ne_zero (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    denominator b p d ≠ 0 :=
  IntegralParameterInverse.charpoly_denominator_ne_zero b.basis (p.coeff d)

omit [Nontrivial A] in
theorem recover [CharZero K] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hdN : d ≤ N) (φ : A →ₐ[ℤ] K) (t : K) (hd : (p.map φ.toRingHom).natDegree = d)
    (hpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    evaluate p d N hdN φ t hd hpos ht (numerator b p d) / ((denominator b p d : ℤ) : K) = t := by
  have H := IntegralParameterInverse.recover_algebra_value b.basis (p.coeff d) φ
    (IntegralParameterExtension.selected_coefficient_ne_zero p d φ hd hpos) t
  simp only [numerator, map_mul, evaluate_root, evaluate_of, ← Polynomial.aeval_algHom_apply]
  exact H

noncomputable def numeratorPolynomial (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    MvPolynomial (Fin (m + 1)) ℤ := (coordinateBasis b p d).representative (numerator b p d)

theorem numeratorPolynomial_degree (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ) :
    (numeratorPolynomial b p d).totalDegree ≤ (m + 1) * (N - 1) :=
  (coordinateBasis b p d).representative_degree _

theorem numeratorPolynomial_support (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (e : Fin (m + 1) →₀ ℕ) (he : e ∈ (numeratorPolynomial b p d).support) (i : Fin (m + 1)) : e i < N :=
  (coordinateBasis b p d).representative_support _ e he i

theorem numeratorPolynomial_recover [CharZero K] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hdN : d ≤ N) (φ : A →ₐ[ℤ] K) (t : K) (hd : (p.map φ.toRingHom).natDegree = d)
    (hpos : 1 ≤ d) (ht : p.eval₂ φ.toRingHom t = 0) :
    (numeratorPolynomial b p d).aeval
      (fun i => evaluate p d N hdN φ t hd hpos ht ((coordinateBasis b p d).generator i)) /
      ((denominator b p d : ℤ) : K) = t := by
  have H := MvPolynomial.comp_aeval_apply (φ := evaluate p d N hdN φ t hd hpos ht)
    (p := numeratorPolynomial b p d) (f := (coordinateBasis b p d).generator)
  have HE : (numeratorPolynomial b p d).aeval (coordinateBasis b p d).generator = numerator b p d :=
    (coordinateBasis b p d).representative_eval (numerator b p d)
  rw [HE] at H
  rw [← H]
  exact recover b p d hdN φ t hd hpos ht

theorem numeratorPolynomial_coefficient (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hN : 0 < N) (e : Fin (m + 1) → Fin N) :
    (numeratorPolynomial b p d).coeff (IntegralCoordinateBasis.exponent e) =
      Algebra.leftMulMatrix (coordinateBasis b p d).basis (numerator b p d) e
        (IntegralCoordinateBasis.zeroIndex (m + 1) N hN) :=
  (coordinateBasis b p d).coefficient_matrix hN (numerator b p d) e

end LeanCanny.Algebra.PaddedIntegralParameterExtension
