/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayQuotientSpecialization
public import LeanCanny.Algebra.MacaulayRoots

/-! # Common roots and the polynomial Macaulay quotient

The active determinant vanishes at every nonzero common homogeneous root
over a domain. If the extraneous determinant is nonzero, so does the
polynomial quotient. For roots on the last coordinate axis, a deformation
of all preceding inputs proves quotient vanishing even when the original
extraneous determinant is zero. General projective roots remain open.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [CommRing K] [IsDomain K]

theorem active_det_eq_zero_of_common_root (p : Fin n → MvPolynomial (Fin n) K) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (x : Fin n → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) (hnz : ∃ j, x j ≠ 0) :
    (activeMinor p d W).det = 0 := by
  have he := PrincipalPadding.determinant (matrix p d W) (activeIndices d W)
  rw [matrix_active_padding] at he
  exact he.symm.trans (det_eq_zero_of_common_root p d W hp hW x hx hnz)

end LeanCanny.Algebra.Macaulay

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [CommRing K] [IsDomain K]

theorem polynomialValue_eq_zero_of_common_root_of_extraneous_ne_zero (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0) (hnz : ∃ j, x j ≠ 0)
    (he : (Macaulay.extraneousMinor p d W).det ≠ 0) : polynomialValue d W hdegree hW p = 0 := by
  have hz := Macaulay.active_det_eq_zero_of_common_root p d W hp hW x hx hnz
  rw [polynomialValue_factorization d W hdegree hW p hp hd] at hz
  exact (mul_eq_zero.mp hz).resolve_left he

noncomputable def lastFixedSystem (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (d : Fin (n + 1) → ℕ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial K) :=
  fun i => if i = Fin.last n then (p i).map Polynomial.C else Macaulay.subtractiveSystem p d i

omit [IsDomain K] in
theorem lastFixedSystem_homogeneous (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (d : Fin (n + 1) → ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (i : Fin (n + 1)) : (lastFixedSystem p d i).IsHomogeneous (d i) := by
  unfold lastFixedSystem
  split
  · exact (hp i).map Polynomial.C
  · exact Macaulay.subtractiveSystem_homogeneous p d hp i

omit [IsDomain K] in
theorem lastFixedSystem_extraneous (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (d : Fin (n + 1) → ℕ) (W : ℕ) :
    Macaulay.extraneousMinor (lastFixedSystem p d) d W =
      AffineCharacteristic.subtractiveMatrix (Macaulay.extraneousMinor p d W) := by
  rw [← Macaulay.extraneousMinor_subtractiveSystem]
  apply Macaulay.extraneousMinor_eq_off_last _ _ d W (Fin.last n) (fun j => Fin.le_last j)
  intro i hi
  simp only [lastFixedSystem, ite_eq_right hi]

omit [IsDomain K] in
theorem lastFixedSystem_eval_zero (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (d : Fin (n + 1) → ℕ) :
    (fun i => (lastFixedSystem p d i).map (Polynomial.evalRingHom (0 : K))) = p := by
  funext i
  by_cases hi : i = Fin.last n
  · ext m
    simp [lastFixedSystem, hi, MvPolynomial.coeff_map]
  · simpa only [lastFixedSystem, ite_eq_right hi] using congrFun (subtractiveSystem_eval_zero p d) i

theorem polynomialValue_eq_zero_of_last_axis_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = 0)
    (hlast : x (Fin.last n) ≠ 0) (haxis : ∀ i, i ≠ Fin.last n → x i = 0) :
    polynomialValue d W hdegree hW p = 0 := by
  have hmap (i : Fin (n + 1)) :
      MvPolynomial.eval (fun j => Polynomial.C (x j)) ((p i).map Polynomial.C) = 0 := by
    have he := MvPolynomial.eval₂_comp (Polynomial.C : K →+* Polynomial K) x (p i)
    rw [hx i, map_zero] at he
    simpa only [MvPolynomial.eval_map, Function.comp_def] using he.symm
  have hroot (i : Fin (n + 1)) :
      MvPolynomial.eval (fun j => Polynomial.C (x j)) (lastFixedSystem p d i) = 0 := by
    by_cases hi : i = Fin.last n
    · simpa only [lastFixedSystem, ite_eq_left hi] using hmap i
    · rw [lastFixedSystem, ite_eq_right hi, Macaulay.subtractiveSystem, map_sub, hmap i]
      simp [MvPolynomial.eval_monomial, haxis i hi, ne_of_gt (hd i)]
  have hz := polynomialValue_eq_zero_of_common_root_of_extraneous_ne_zero d W hdegree hW
    (lastFixedSystem p d) (lastFixedSystem_homogeneous p d hp) hd (fun j => Polynomial.C (x j)) hroot
    ⟨Fin.last n, Polynomial.C_ne_zero.mpr hlast⟩ (by
      rw [lastFixedSystem_extraneous]
      exact AffineCharacteristic.subtractive_det_ne_zero _)
  have he := polynomialValue_map (Polynomial.evalRingHom (0 : K)) d W hdegree hW (lastFixedSystem p d)
  rw [hz, map_zero, lastFixedSystem_eval_zero] at he
  exact he.symm

theorem eval_characteristicQuotient_eq_zero_of_last_axis_root (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (s : K) (x : Fin (n + 1) → K) (hx : ∀ i, MvPolynomial.eval x (p i) = s * x i ^ d i)
    (hlast : x (Fin.last n) ≠ 0) (haxis : ∀ i, i ≠ Fin.last n → x i = 0) :
    Polynomial.eval s (Macaulay.characteristicQuotient p d W) = 0 := by
  rw [eval_characteristicQuotient d W hdegree hW p hp hd s]
  apply polynomialValue_eq_zero_of_last_axis_root d W hdegree hW _ _ hd x _ hlast haxis
  · intro i
    exact (hp i).sub (MvPolynomial.isHomogeneous_monomial s (Finsupp.degree_single i (d i)))
  · intro i
    simp [hx i, MvPolynomial.eval_monomial]

end LeanCanny.Algebra.MacaulayUniversal
