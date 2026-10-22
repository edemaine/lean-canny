/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantRoot
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# First subresultants after removing a linear common factor

Removing `X-b` from both inputs turns the leading first-subresultant minor
into the quotient Sylvester matrix by an upper triangular transformation with
diagonal entries one. Its determinant is therefore the quotient resultant.
-/

@[expose] public section

namespace LeanCanny.Algebra.Subresultant
open Polynomial
open scoped BigOperators

def linearFactorMatrix {R : Type*} [CommRing R] (s : ℕ) (b : R) : Matrix (Fin s) (Fin s) R :=
  fun i => Pi.single i 1 - if h : i.val + 1 < s then Pi.single ⟨i.val + 1, h⟩ b else 0

theorem linearFactorMatrix_mul {R : Type*} [CommRing R] {s : ℕ} (b : R)
    (M : Matrix (Fin s) (Fin s) R) (i j : Fin s) :
    (linearFactorMatrix s b * M) i j = M i j -
      if h : i.val + 1 < s then b * M ⟨i.val + 1, h⟩ j else 0 := by
  change (linearFactorMatrix s b i) ⬝ᵥ (fun k => M k j) = _
  rw [linearFactorMatrix, sub_dotProduct, single_dotProduct, one_mul]
  by_cases hi : i.val + 1 < s <;> simp [hi, single_dotProduct]

theorem linearFactorMatrix_det {R : Type*} [CommRing R] (s : ℕ) (b : R) :
    (linearFactorMatrix s b).det = 1 := by
  have ht : (linearFactorMatrix s b).IsUpperTriangular := by
    intro i j hji
    change j.val < i.val at hji
    have hij : i ≠ j := ne_of_gt hji
    by_cases hi : i.val + 1 < s
    · have hnext : (⟨i.val + 1, hi⟩ : Fin s) ≠ j := by
        intro h
        have he : i.val + 1 = j.val := congrArg Fin.val h
        omega
      simp [linearFactorMatrix, hi, hij, hnext]
    · simp [linearFactorMatrix, hi, hij]
  rw [Matrix.det_of_isUpperTriangular ht]
  have hd : ∀ i : Fin s, linearFactorMatrix s b i i = 1 := by
    intro i
    by_cases hi : i.val + 1 < s
    · have hnext : (⟨i.val + 1, hi⟩ : Fin s) ≠ i := by
        intro h
        have he : i.val + 1 = i.val := congrArg Fin.val h
        omega
      simp [linearFactorMatrix, hi, hnext]
    · simp [linearFactorMatrix, hi]
  simp only [hd, Finset.prod_const_one]

theorem sylvester_apply_eq_shifted_coeff {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (i j : Fin (m + n)) :
    Polynomial.sylvester f g m n i j =
      (j.addCases (fun j => g * X ^ j.val) (fun j => f * X ^ j.val) : Polynomial R).coeff i.val := by
  induction j using Fin.addCases with
  | left j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left, Set.mem_Icc]
    change band g n i.val j.val = (g * X ^ j.val).coeff i.val
    exact band_eq_coeff_mul_X_pow g n i.val j.val hg
  | right j =>
    simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right, Set.mem_Icc]
    change band f m i.val j.val = (f * X ^ j.val).coeff i.val
    exact band_eq_coeff_mul_X_pow f m i.val j.val hf

theorem shiftedColumns_linear_factor {R : Type*} [CommRing R] (f g : Polynomial R) (m n : ℕ) (b : R)
    (j : Fin ((m - 1) + (n - 1))) :
    shiftedColumns ((X - C b) * f) ((X - C b) * g) m n j =
      (X - C b) * shiftedColumns f g m n j := by
  induction j using Fin.addCases <;> simp only [shiftedColumns, Fin.addCases_left, Fin.addCases_right, mul_assoc]

theorem shiftedColumns_quotient_degree {R : Type*} [Semiring R] [Nontrivial R]
    (f g : Polynomial R) (m n : ℕ) (hf : f.natDegree ≤ m - 1) (hg : g.natDegree ≤ n - 1)
    (j : Fin ((m - 1) + (n - 1))) :
    (shiftedColumns f g m n j).natDegree < (m - 1) + (n - 1) := by
  induction j using Fin.addCases with
  | left j =>
    have h : (g * X ^ j.val).natDegree ≤ g.natDegree + (X ^ j.val : Polynomial R).natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_X_pow] at h
    have hj := j.is_lt
    simpa only [shiftedColumns, Fin.addCases_left] using (show (g * X ^ j.val).natDegree < (m - 1) + (n - 1) by omega)
  | right j =>
    have h : (f * X ^ j.val).natDegree ≤ f.natDegree + (X ^ j.val : Polynomial R).natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_X_pow] at h
    have hj := j.is_lt
    simpa only [shiftedColumns, Fin.addCases_right] using (show (f * X ^ j.val).natDegree < (m - 1) + (n - 1) by omega)

theorem minor_first_one_linear_factor {R : Type*} [CommRing R] [Nontrivial R]
    (f g : Polynomial R) (m n : ℕ) (b : R)
    (hf : f.natDegree ≤ m - 1) (hg : g.natDegree ≤ n - 1)
    (hF : ((X - C b) * f).natDegree ≤ m) (hG : ((X - C b) * g).natDegree ≤ n) :
    minor ((X - C b) * f) ((X - C b) * g) m n 1 1 =
      linearFactorMatrix ((m - 1) + (n - 1)) b * Polynomial.sylvester f g (m - 1) (n - 1) := by
  funext i j
  rw [minor_first_apply _ _ _ _ _ hF hG, rowIndex_one, shiftedColumns_linear_factor,
    Polynomial.coeff_X_sub_C_mul, linearFactorMatrix_mul,
    sylvester_apply_eq_shifted_coeff f g _ _ hf hg]
  change _ = (shiftedColumns f g m n j).coeff i.val - _
  by_cases hi : i.val + 1 < (m - 1) + (n - 1)
  · rw [dite_eq_left hi, sylvester_apply_eq_shifted_coeff f g _ _ hf hg]
    rfl
  · have hz : (shiftedColumns f g m n j).coeff (i.val + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by
      have := shiftedColumns_quotient_degree f g m n hf hg j
      omega)
    rw [dite_eq_right hi, hz, mul_zero]

theorem minor_first_one_det_linear_factor {R : Type*} [CommRing R] [Nontrivial R]
    (f g : Polynomial R) (m n : ℕ) (b : R)
    (hf : f.natDegree ≤ m - 1) (hg : g.natDegree ≤ n - 1)
    (hF : ((X - C b) * f).natDegree ≤ m) (hG : ((X - C b) * g).natDegree ≤ n) :
    (minor ((X - C b) * f) ((X - C b) * g) m n 1 1).det = f.resultant g (m - 1) (n - 1) := by
  rw [minor_first_one_linear_factor f g m n b hf hg hF hG, Matrix.det_mul, linearFactorMatrix_det, one_mul]
  rfl

theorem isCoprime_quotients_of_linear_gcd {K : Type*} [Field K] [DecidableEq K]
    (f g F G : Polynomial K) (b l : K) (hl : l ≠ 0)
    (hf : f = (X - C b) * F) (hg : g = (X - C b) * G)
    (hcommon : EuclideanDomain.gcd f g = C l * (X - C b)) : IsCoprime F G := by
  classical
  let a := EuclideanDomain.gcdA f g
  let d := EuclideanDomain.gcdB f g
  have he : (X - C b) * (F * a + G * d) = (X - C b) * C l := by
    calc
      (X - C b) * (F * a + G * d) = f * a + g * d := by rw [hf, hg]; ring
      _ = EuclideanDomain.gcd f g := (EuclideanDomain.gcd_eq_gcd_ab f g).symm
      _ = (X - C b) * C l := by rw [hcommon, mul_comm]
  have hc : F * a + G * d = C l := mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero b) he
  refine ⟨C l⁻¹ * a, C l⁻¹ * d, ?_⟩
  calc
    C l⁻¹ * a * F + C l⁻¹ * d * G = C l⁻¹ * (F * a + G * d) := by ring
    _ = C l⁻¹ * C l := by rw [hc]
    _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hl, map_one]

theorem minor_first_one_det_ne_zero_of_linear_gcd {K : Type*} [Field K] [DecidableEq K]
    (f g : Polynomial K) (b l : K) (hl : l ≠ 0)
    (hcommon : EuclideanDomain.gcd f g = C l * (X - C b)) :
    (minor f g f.natDegree g.natDegree 1 1).det ≠ 0 := by
  classical
  have hroot : (EuclideanDomain.gcd f g).IsRoot b := by rw [hcommon]; simp
  obtain ⟨hfb, hgb⟩ := Polynomial.isRoot_gcd_iff_isRoot_left_right.mp hroot
  let F := f /ₘ (X - C b)
  let G := g /ₘ (X - C b)
  have hF : (X - C b) * F = f := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hfb
  have hG : (X - C b) * G = g := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hgb
  have hFd : F.natDegree = f.natDegree - 1 := by
    dsimp [F]
    rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C b), Polynomial.natDegree_X_sub_C]
  have hGd : G.natDegree = g.natDegree - 1 := by
    dsimp [G]
    rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C b), Polynomial.natDegree_X_sub_C]
  have hc := isCoprime_quotients_of_linear_gcd f g F G b l hl hF.symm hG.symm hcommon
  have he := minor_first_one_det_linear_factor F G f.natDegree g.natDegree b hFd.le hGd.le
    (by rw [hF]) (by rw [hG])
  rw [hF, hG] at he
  rw [he]
  simpa only [← hFd, ← hGd] using Polynomial.resultant_ne_zero F G hc

theorem first_spec_of_linear_gcd {K : Type*} [Field K] [DecidableEq K]
    (f g : Polynomial K) (b l : K) (hl : l ≠ 0)
    (hm : 1 < f.natDegree) (hn : 1 < g.natDegree)
    (hcommon : EuclideanDomain.gcd f g = C l * (X - C b)) :
    let S := polynomial f g f.natDegree g.natDegree 1
    S.natDegree = 1 ∧ S.coeff 1 ≠ 0 ∧ b = -S.coeff 0 / S.coeff 1 := by
  classical
  have hroot : (EuclideanDomain.gcd f g).IsRoot b := by rw [hcommon]; simp
  obtain ⟨hfb, hgb⟩ := Polynomial.isRoot_gcd_iff_isRoot_left_right.mp hroot
  have hden := minor_first_one_det_ne_zero_of_linear_gcd f g b l hl hcommon
  have hlin := first_eq_mul_X_sub_C f g f.natDegree g.natDegree b hm hn le_rfl le_rfl hfb hgb
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [hlin, Polynomial.natDegree_C_mul hden, Polynomial.natDegree_X_sub_C]
  · simpa only [coeff, hm, hn, le_refl, and_self, ↓reduceIte] using hden
  · simpa only [coeff, hm, hn, Nat.zero_le, le_refl, and_self, ↓reduceIte] using
      root_eq_neg_div f g f.natDegree g.natDegree b hm hn le_rfl le_rfl hfb hgb hden

end LeanCanny.Algebra.Subresultant
