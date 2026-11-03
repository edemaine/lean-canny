/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BivariateSquareTopCoefficient
/-! # Row weights preserve real zeros of the Gram value leading coefficient

The value variable may be multiplied by a nonzero real constant. Every row
has its own nonzero real weight; their squares cannot cancel in the actual
Gram determinant. The sweep parameter remains the inner polynomial variable.
-/
@[expose] public section
namespace LeanCanny.Algebra.GramLeadingCoefficientCovariance
open Polynomial Matrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

noncomputable def minors (A : Matrix ι κ (Polynomial ℝ)[X]) (f : κ→ι) :=
  (A.submatrix f id).det
noncomputable def gram (A : Matrix ι κ (Polynomial ℝ)[X]) := (A.transpose*A).det
noncomputable def rescale (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ) :
    Matrix ι κ (Polynomial ℝ)[X] :=fun i j=>C (C (w i))*(A i j).comp (C (C H)*X)
noncomputable def weights (w : ι→ℝ) (f : κ→ι) := ∏i,w (f i)

omit [Fintype ι] in
theorem minors_rescale (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ) :
    minors (rescale A w H)=BivariateSquareTopCoefficient.rescale (minors A) (weights w) H :=by
  funext f
  let ρ:=Polynomial.compRingHom (C (C H)*X : (Polynomial ℝ)[X])
  have HW : (∏i,C (C (w (f i))))=C (C (weights w f)):=by
    simp only [weights,map_prod]
  calc
    _=(∏i,C (C (w (f i))))*((A.submatrix f id).map ρ).det:=
      Matrix.det_mul_column (fun i=>C (C (w (f i)))) ((A.submatrix f id).map ρ)
    _=(∏i,C (C (w (f i))))*ρ ((A.submatrix f id).det):=
      congrArg ((∏i,C (C (w (f i))))*·) (ρ.map_det (A.submatrix f id)).symm
    _=_:=by rw [HW];rfl

theorem squares_minors (A : Matrix ι κ (Polynomial ℝ)[X]) :
    BivariateSquareTopCoefficient.squares (minors A)=
      C ((Fintype.card κ).factorial : Polynomial ℝ)*gram A :=by
  exact (GramDeterminantSquares.factorial_mul A).symm

theorem coefficient_eval_zero_iff (A : Matrix ι κ (Polynomial ℝ)[X]) (d : ℕ) (t : ℝ) :
    ((gram A).coeff d).eval t=0 ↔
      ((BivariateSquareTopCoefficient.squares (minors A)).coeff d).eval t=0 :=by
  rw [squares_minors,Polynomial.coeff_C_mul,Polynomial.eval_mul,Polynomial.eval_natCast]
  have HN : ((Fintype.card κ).factorial : ℝ)≠0:=Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  simp only [mul_eq_zero,HN,false_or]

theorem top_zero_iff (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (d : ℕ) (hd : ∀f,(minors A f).natDegree≤d) (t : ℝ) :
    ((gram (rescale A w H)).coeff (2*d)).eval t=0 ↔ ((gram A).coeff (2*d)).eval t=0 :=by
  rw [coefficient_eval_zero_iff,coefficient_eval_zero_iff A,minors_rescale]
  exact BivariateSquareTopCoefficient.rescale_eval_zero_iff (minors A) (weights w) H
    (fun f=>Finset.prod_ne_zero_iff.mpr (fun i _=>hw (f i))) hH d hd t

theorem squares_degree (A : Matrix ι κ (Polynomial ℝ)[X]) :
    (BivariateSquareTopCoefficient.squares (minors A)).natDegree=(gram A).natDegree :=by
  rw [squares_minors,Polynomial.natDegree_C_mul]
  exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

theorem degree_eq (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (d : ℕ) (hd : ∀f,(minors A f).natDegree≤d)
    (hi : ∃f,(minors A f).coeff d≠0) :
    (gram (rescale A w H)).natDegree=(gram A).natDegree :=by
  have HE:=BivariateSquareTopCoefficient.rescale_degree_eq (minors A) (weights w) H
    (fun f=>Finset.prod_ne_zero_iff.mpr (fun i _=>hw (f i))) hH d hd hi
  rw [←minors_rescale,squares_degree,squares_degree] at HE
  exact HE

theorem leading_zero_iff (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (d : ℕ) (hd : ∀f,(minors A f).natDegree≤d)
    (hi : ∃f,(minors A f).coeff d≠0) (t : ℝ) :
    (gram (rescale A w H)).leadingCoeff.eval t=0 ↔ (gram A).leadingCoeff.eval t=0 :=by
  have HA : (gram A).natDegree=2*d:=(squares_degree A).symm.trans
    (BivariateSquareTopCoefficient.degree_eq (minors A) d hd hi)
  have HB : (gram (rescale A w H)).natDegree=2*d:=
    (degree_eq A w H hw hH d hd hi).trans HA
  simpa only [Polynomial.leadingCoeff,HA,HB] using top_zero_iff A w H hw hH d hd t

theorem exists_minor_degree (A : Matrix ι κ (Polynomial ℝ)[X]) (hA : gram A≠0) :
    ∃d : ℕ,(∀f,(minors A f).natDegree≤d) ∧ ∃f,(minors A f).coeff d≠0 :=by
  have HF : ∃f,minors A f≠0:=by
    by_contra HN
    push Not at HN
    have HE:=squares_minors A
    have HZ : BivariateSquareTopCoefficient.squares (minors A)=0:=by
      simp only [BivariateSquareTopCoefficient.squares,HN,zero_pow (by decide : 2≠0),Finset.sum_const_zero]
    rw [HZ] at HE
    have Hfac : ((Fintype.card κ).factorial : Polynomial ℝ)≠0:=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    exact hA ((mul_eq_zero.mp HE.symm).resolve_left (Polynomial.C_ne_zero.mpr Hfac))
  obtain ⟨f,hf⟩:=HF
  let d:=Finset.univ.sup (fun f : κ→ι=>(minors A f).natDegree)
  have HD (g : κ→ι) : (minors A g).natDegree≤d:=
    Finset.le_sup (f:=fun g=>(minors A g).natDegree) (Finset.mem_univ g)
  by_cases HZ : d=0
  · refine ⟨d,HD,f,?_⟩
    intro HC
    apply hf
    have HG : (minors A f).natDegree=0:=by have HB:=HD f;omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero HG]
    have HC0 : (minors A f).coeff 0=0:=by simpa only [HZ] using HC
    rw [HC0,Polynomial.C_0]
  · obtain ⟨g,_,HG⟩:=Finset.exists_mem_eq_sup (Finset.univ : Finset (κ→ι)) ⟨f,Finset.mem_univ f⟩
      (fun g=>(minors A g).natDegree)
    change d=(minors A g).natDegree at HG
    refine ⟨d,HD,g,?_⟩
    rw [HG,Polynomial.coeff_natDegree]
    apply Polynomial.leadingCoeff_ne_zero.mpr
    intro HC
    exact HZ (by simpa only [HC,Polynomial.natDegree_zero] using HG)

theorem degree_eq_of_ne_zero (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (hA : gram A≠0) :
    (gram (rescale A w H)).natDegree=(gram A).natDegree :=by
  obtain ⟨d,hd,hi⟩:=exists_minor_degree A hA
  exact degree_eq A w H hw hH d hd hi

theorem leading_zero_iff_of_ne_zero (A : Matrix ι κ (Polynomial ℝ)[X]) (w : ι→ℝ) (H : ℝ)
    (hw : ∀i,w i≠0) (hH : H≠0) (hA : gram A≠0) (t : ℝ) :
    (gram (rescale A w H)).leadingCoeff.eval t=0 ↔ (gram A).leadingCoeff.eval t=0 :=by
  obtain ⟨d,hd,hi⟩:=exists_minor_degree A hA
  exact leading_zero_iff A w H hw hH d hd hi t

end LeanCanny.Algebra.GramLeadingCoefficientCovariance
