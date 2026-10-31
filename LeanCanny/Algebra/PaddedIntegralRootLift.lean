/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterExtension
public import LeanCanny.Algebra.MonicParameterRows

/-! # Interpreting every root of a canonical padded scalar equation

Any root extends the old integral-algebra evaluation, including extra zero
branches introduced by padding. Interpreting a root does not require a
selected coefficient to be invertible or the old algebra to be reduced.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedDegreeIntegralNormalization
open Polynomial
open scoped Classical
variable {R : Type*} [CommRing R]

theorem eq_of_monic (p : Polynomial R) (d : ℕ) (hp : p.Monic) (hd : p.natDegree = d) : polynomial p d = p := by
  have HC : p.coeff d = 1 := by rw [← hd, Polynomial.coeff_natDegree, hp.leadingCoeff]
  ext i
  rw [coefficient, HC, one_pow, mul_one]
  by_cases hi : i = d
  · subst i
    simp only [ite_true, Nat.lt_irrefl, ite_false, add_zero, HC]
  · rw [ite_eq_right hi, zero_add]
    by_cases hlt : i < d
    · rw [ite_eq_left hlt]
    · rw [ite_eq_right hlt, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

end LeanCanny.Algebra.FixedDegreeIntegralNormalization

namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A K : Type*} [CommRing A] [CommRing K] {m N : ℕ}

noncomputable def liftAtRoot (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (φ : A →ₐ[ℤ] K) (z : K)
    (hz : (equation b p d).eval₂ (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom z = 0) :
    Extension p d N →ₐ[ℤ] K :=
  AdjoinRoot.liftAlgHom _ φ z (by
    change (PaddedIntegralNormalization.polynomial p d N).eval₂ φ.toRingHom z = 0
    have HE := b.polynomial_eval (PaddedIntegralNormalization.polynomial p d N) φ z
    exact HE.symm.trans hz)

theorem liftAtRoot_of (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (φ : A →ₐ[ℤ] K) (z : K) hz (a : A) : liftAtRoot b p d φ z hz (AdjoinRoot.of _ a) = φ a :=
  AdjoinRoot.liftAlgHom_of _ φ _ _ a

theorem liftAtRoot_root (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (φ : A →ₐ[ℤ] K) (z : K) hz : liftAtRoot b p d φ z hz (AdjoinRoot.root _) = z :=
  AdjoinRoot.liftAlgHom_root _ φ _ _

theorem liftAtRoot_generators [Nontrivial A] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (φ : A →ₐ[ℤ] K) (z : K) hz (i : Fin (m + 1)) :
    liftAtRoot b p d φ z hz ((coordinateBasis b p d).generator i) = (Fin.cons z (fun j : Fin m => φ (b.generator j)) : Fin (m + 1) → K) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change liftAtRoot b p d φ z hz (AdjoinRoot.root _) = z
    exact liftAtRoot_root b p d φ z hz
  · change liftAtRoot b p d φ z hz (AdjoinRoot.of _ (b.generator j)) = φ (b.generator j)
    exact liftAtRoot_of b p d φ z hz _

theorem powered_row_root [Nontrivial A] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hN : 0 < N) (w : Fin m → ℕ) (W : ℕ) (z : (Fin m ⊕ Unit) → K)
    (hz : (MonicParameterRows.row (equation b p d) N w W).eval₂ (Int.castRingHom K) z = 0) :
    (equation b p d).eval₂
      (MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i => z (Sum.inl i) ^ w i)) (z (Sum.inr ()) ^ W) = 0 := by
  rw [MonicParameterRows.eval_row, FixedDegreeIntegralNormalization.eq_of_monic _ N
    (equation_monic b p d hN).1 (equation_monic b p d hN).2] at hz
  exact hz

theorem powered_row_root_at_evaluation [Nontrivial A] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hN : 0 < N) (φ : A →ₐ[ℤ] K) (w : Fin m → ℕ) (W : ℕ) (z : (Fin m ⊕ Unit) → K)
    (hold : ∀ i, φ (b.generator i) = z (Sum.inl i) ^ w i)
    (hz : (MonicParameterRows.row (equation b p d) N w W).eval₂ (Int.castRingHom K) z = 0) :
    (equation b p d).eval₂ (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom
      (z (Sum.inr ()) ^ W) = 0 := by
  have H := powered_row_root b p d hN w W z hz
  have HC : MvPolynomial.eval₂Hom (Int.castRingHom K) (fun i => z (Sum.inl i) ^ w i) =
      (MvPolynomial.aeval (fun i => φ (b.generator i))).toRingHom := by
    change MvPolynomial.eval₂Hom (algebraMap ℤ K) (fun i => z (Sum.inl i) ^ w i) =
      MvPolynomial.eval₂Hom (algebraMap ℤ K) (fun i => φ (b.generator i))
    congr 1
    funext i
    exact (hold i).symm
  rw [HC] at H
  exact H

noncomputable def liftAtPoweredRoot [Nontrivial A] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hN : 0 < N) (φ : A →ₐ[ℤ] K) (w : Fin m → ℕ) (W : ℕ) (z : (Fin m ⊕ Unit) → K)
    (hold : ∀ i, φ (b.generator i) = z (Sum.inl i) ^ w i)
    (hz : (MonicParameterRows.row (equation b p d) N w W).eval₂ (Int.castRingHom K) z = 0) :
    Extension p d N →ₐ[ℤ] K :=
  liftAtRoot b p d φ (z (Sum.inr ()) ^ W) (powered_row_root_at_evaluation b p d hN φ w W z hold hz)

theorem liftAtPoweredRoot_generators [Nontrivial A] (b : IntegralCoordinateBasis A m N) (p : Polynomial A) (d : ℕ)
    (hN : 0 < N) (φ : A →ₐ[ℤ] K) (w : Fin m → ℕ) (W : ℕ) (z : (Fin m ⊕ Unit) → K) hold hz :
    (fun i => liftAtPoweredRoot b p d hN φ w W z hold hz ((coordinateBasis b p d).generator i)) =
      Fin.cons (z (Sum.inr ()) ^ W) (fun j => z (Sum.inl j) ^ w j) := by
  funext i
  rw [liftAtPoweredRoot, liftAtRoot_generators]
  exact Fin.cases rfl (fun j => hold j) i

end LeanCanny.Algebra.PaddedIntegralParameterExtension
