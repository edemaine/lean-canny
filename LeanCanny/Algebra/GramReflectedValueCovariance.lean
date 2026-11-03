/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.GramLeadingCoefficientCovariance
public import LeanCanny.Algebra.ReflectedValueTrailing
/-! # The actual reflected Gram value certificate preserves its trailing cut

Both the selected trailing index and the real zero set of its coefficient
survive nonzero constant row weights and value dilation. These are the two
properties needed by the selected equation-value bad cut.
-/
@[expose] public section
namespace LeanCanny.Algebra.GramLeadingCoefficientCovariance
open Polynomial Matrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem rescale_ne_zero (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (hA : gram A≠0) : gram (rescale A w H)≠0 :=by
  obtain ⟨d,hd,f,hf⟩:=exists_minor_degree A hA
  have HW (g : κ→ι) : weights w g≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hw (g i))
  have HC:=BivariateSquareTopCoefficient.coefficient_ne_zero
    (BivariateSquareTopCoefficient.rescale (minors A) (weights w) H) d
    (BivariateSquareTopCoefficient.rescale_degree_le _ _ _ d hd)
    ⟨f,fun hz=>hf ((BivariateSquareTopCoefficient.rescale_coefficient_zero_iff
      (minors A) (weights w) H HW hH d f).mp hz)⟩
  rw [←minors_rescale] at HC
  intro HZ
  rw [squares_minors,HZ,mul_zero,Polynomial.coeff_zero] at HC
  exact HC rfl

theorem reflected_trailing_degree (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (hA : gram A≠0) (D : ℕ) (hd : (gram A).natDegree≤D) :
    (X*(gram (rescale A w H)).reflect D).natTrailingDegree=
      (X*(gram A).reflect D).natTrailingDegree :=by
  have HE:=degree_eq_of_ne_zero A w H hw hH hA
  rw [ReflectedValueTrailing.trailing_degree _ (rescale_ne_zero A w H hw hH hA) D (HE.trans_le hd),
    ReflectedValueTrailing.trailing_degree _ hA D hd,HE]

theorem reflected_trailing_zero_iff (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (hA : gram A≠0) (D : ℕ) (hd : (gram A).natDegree≤D) (t : ℝ) :
    (X*(gram (rescale A w H)).reflect D).trailingCoeff.eval t=0 ↔
      (X*(gram A).reflect D).trailingCoeff.eval t=0 :=by
  have HE:=degree_eq_of_ne_zero A w H hw hH hA
  rw [ReflectedValueTrailing.trailing_coefficient _ (rescale_ne_zero A w H hw hH hA) D (HE.trans_le hd),
    ReflectedValueTrailing.trailing_coefficient _ hA D hd]
  exact leading_zero_iff_of_ne_zero A w H hw hH hA t

end LeanCanny.Algebra.GramLeadingCoefficientCovariance
