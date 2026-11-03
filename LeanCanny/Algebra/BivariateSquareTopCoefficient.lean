/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.GramDeterminantSquares
/-! # Real zeros of the top coefficient of a sum of polynomial squares

The outer variable is the value parameter; coefficients are real sweep
polynomials. Positivity prevents cancellation between maximal minors.
-/
@[expose] public section
namespace LeanCanny.Algebra.BivariateSquareTopCoefficient
open Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {J : Type*} [Fintype J]

noncomputable def squares (p : J→(Polynomial ℝ)[X]) := ∑i,p i^2

theorem coefficient (p : J→(Polynomial ℝ)[X]) (d : ℕ)
    (hd : ∀i,(p i).natDegree≤d) :
    (squares p).coeff (2*d)=∑i,((p i).coeff d)^2 :=by
  simp only [squares,Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_two,show 2*d=d+d by omega,
    Polynomial.coeff_mul_add_eq_of_natDegree_le (hd i) (hd i),pow_two]

theorem eval_zero_iff (p : J→(Polynomial ℝ)[X]) (d : ℕ)
    (hd : ∀i,(p i).natDegree≤d) (t : ℝ) :
    ((squares p).coeff (2*d)).eval t=0 ↔ ∀i,((p i).coeff d).eval t=0 :=by
  rw [coefficient p d hd,Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_pow]
  simpa only [Finset.mem_univ,forall_true_left] using
    (Finset.sum_sq_eq_zero_iff (Finset.univ : Finset J) (fun i=>((p i).coeff d).eval t))

theorem coefficient_ne_zero (p : J→(Polynomial ℝ)[X]) (d : ℕ)
    (hd : ∀i,(p i).natDegree≤d) (hi : ∃i,(p i).coeff d≠0) :
    (squares p).coeff (2*d)≠0 :=by
  intro HZ
  obtain ⟨i,hi⟩:=hi
  apply hi
  apply Polynomial.funext
  intro t
  have HE:=((eval_zero_iff p d hd t).mp (by rw [HZ,Polynomial.eval_zero])) i
  simpa only [Polynomial.eval_zero] using HE

theorem degree_eq (p : J→(Polynomial ℝ)[X]) (d : ℕ)
    (hd : ∀i,(p i).natDegree≤d) (hi : ∃i,(p i).coeff d≠0) :
    (squares p).natDegree=2*d :=by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (Polynomial.natDegree_pow_le).trans (Nat.mul_le_mul_left 2 (hd i))
  · exact coefficient_ne_zero p d hd hi

noncomputable def rescale (p : J→(Polynomial ℝ)[X]) (w : J→ℝ) (H : ℝ) (i : J) :
    (Polynomial ℝ)[X] := C (C (w i))*(p i).comp (C (C H)*X)

omit [Fintype J] in
theorem rescale_degree_le (p : J→(Polynomial ℝ)[X]) (w : J→ℝ) (H : ℝ)
    (d : ℕ) (hd : ∀i,(p i).natDegree≤d) (i : J) :
    (rescale p w H i).natDegree≤d :=by
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply Polynomial.natDegree_comp_le.trans
  have HL : (C (C H)*X : (Polynomial ℝ)[X]).natDegree≤1:=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp only [natDegree_X]; rfl)
  exact (Nat.mul_le_mul (hd i) HL).trans_eq (Nat.mul_one d)

omit [Fintype J] in
theorem rescale_coefficient (p : J→(Polynomial ℝ)[X]) (w : J→ℝ) (H : ℝ) (d : ℕ) (i : J) :
    (rescale p w H i).coeff d=C (w i)*((p i).coeff d*C H^d) :=by
  simp only [rescale,Polynomial.coeff_C_mul,Polynomial.comp_C_mul_X_coeff]

omit [Fintype J] in
theorem rescale_coefficient_zero_iff (p : J→(Polynomial ℝ)[X]) (w : J→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (d : ℕ) (i : J) :
    (rescale p w H i).coeff d=0 ↔ (p i).coeff d=0 :=by
  rw [rescale_coefficient]
  have HP : (C H : Polynomial ℝ)^d≠0:=pow_ne_zero _ (Polynomial.C_ne_zero.mpr hH)
  simp only [mul_eq_zero,Polynomial.C_eq_zero,hw i,HP,or_false,false_or]

theorem rescale_eval_zero_iff (p : J→(Polynomial ℝ)[X]) (w : J→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (d : ℕ) (hd : ∀i,(p i).natDegree≤d) (t : ℝ) :
    ((squares (rescale p w H)).coeff (2*d)).eval t=0 ↔
      ((squares p).coeff (2*d)).eval t=0 :=by
  rw [eval_zero_iff _ d (rescale_degree_le p w H d hd),eval_zero_iff p d hd]
  apply forall_congr'
  intro i
  rw [rescale_coefficient]
  have HP : H^d≠0:=pow_ne_zero _ hH
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,mul_eq_zero,
    hw i,HP,or_false,false_or]

theorem rescale_degree_eq (p : J→(Polynomial ℝ)[X]) (w : J→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (d : ℕ) (hd : ∀i,(p i).natDegree≤d)
    (hi : ∃i,(p i).coeff d≠0) :
    (squares (rescale p w H)).natDegree=(squares p).natDegree :=by
  rw [degree_eq p d hd hi]
  apply degree_eq _ d (rescale_degree_le p w H d hd)
  obtain ⟨i,hi⟩:=hi
  exact ⟨i,fun h=>hi ((rescale_coefficient_zero_iff p w H hw hH d i).mp h)⟩

end LeanCanny.Algebra.BivariateSquareTopCoefficient
