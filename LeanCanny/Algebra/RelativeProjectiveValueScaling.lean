/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.RelativeProjectiveValueGram
public import LeanCanny.Algebra.MacaulayFullBoxScaling
public import LeanCanny.Algebra.GramReflectedValueCovariance
/-! # Scaling the actual reciprocal value system gives the weighted Gram model

The value row is unweighted and its variable is dilated. Coordinate rows
acquire their common nonzero scale; full-box padding stays at weight one.
-/
@[expose] public section
namespace LeanCanny.Algebra.RelativeProjectiveValueScaling
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def sourceWeight (a : ℝ) : Fin (n+1)→ℝ:=Fin.cases 1 (fun _=>a)
def rowWeight (a : ℝ) (W : ℕ) : MacaulayFullBox.Row (n+1) W→ℝ:=
  MacaulayFullBox.rowWeight (sourceWeight a)

private theorem constant_map (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (s : ℝ) :
    (F.map Polynomial.C).map (Polynomial.compRingHom (C (C s)*X))=F.map Polynomial.C :=by
  rw [MvPolynomial.map_map,Polynomial.compRingHom,Polynomial.eval₂RingHom_comp_C]

theorem system_scale (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial ℝ))
    (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (e : ℕ) (a s : ℝ) :
    RelativeProjectiveValueGram.system (fun i=>MvPolynomial.C (C a)*H i) (MvPolynomial.C (C s)*F) e=
      fun j=>MvPolynomial.C (C (C (sourceWeight a j)))*
        (RelativeProjectiveValueGram.system H F e j).map (Polynomial.compRingHom (C (C s)*X)) :=by
  funext j
  refine Fin.cases ?_ (fun i=>?_) j
  · simp only [RelativeProjectiveValueGram.system,Fin.cases_zero,sourceWeight,
      map_mul,map_sub,MvPolynomial.map_C,map_pow,
      MvPolynomial.map_X,constant_map,Polynomial.C_1,MvPolynomial.C_1,one_mul,
      Polynomial.coe_compRingHom_apply,Polynomial.X_comp]
    ring
  · simp only [RelativeProjectiveValueGram.system,Fin.cases_succ,sourceWeight,
      map_mul,MvPolynomial.map_C,constant_map]

noncomputable def matrix (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial ℝ))
    (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (d : Fin n→ℕ) (e W : ℕ) :=
  MacaulayFullBox.matrix (RelativeProjectiveValueGram.system H F e)
    (RelativeProjectiveValueGram.degrees d e) W

theorem matrix_scale (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial ℝ))
    (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (d : Fin n→ℕ) (e W : ℕ) (a s : ℝ) :
    matrix (fun i=>MvPolynomial.C (C a)*H i) (MvPolynomial.C (C s)*F) d e W=
      GramLeadingCoefficientCovariance.rescale (matrix H F d e W) (rowWeight a W) s :=by
  unfold matrix
  rw [system_scale,MacaulayFullBox.matrix_scale_map]
  funext r c
  have HW : MacaulayFullBox.rowWeight (fun j=>C (C (sourceWeight a j))) r=
      C (C (rowWeight a W r)):=by
    rcases r with ⟨i,r⟩|r
    · rfl
    · simp only [MacaulayFullBox.rowWeight,rowWeight,Polynomial.C_1]
  rw [HW]
  rfl

theorem polynomial_scale (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial ℝ))
    (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (d : Fin n→ℕ) (e W : ℕ) (a s : ℝ) :
    RelativeProjectiveValueGram.polynomial (fun i=>MvPolynomial.C (C a)*H i)
      (MvPolynomial.C (C s)*F) d e W=
      GramLeadingCoefficientCovariance.gram
        (GramLeadingCoefficientCovariance.rescale (matrix H F d e W) (rowWeight a W) s) :=by
  exact congrArg (fun A=>(A.transpose*A).det) (matrix_scale H F d e W a s)

theorem rowWeight_ne_zero (a : ℝ) (ha : a≠0) (W : ℕ) (r : MacaulayFullBox.Row (n+1) W) :
    rowWeight a W r≠0 :=by
  rcases r with ⟨i,r⟩|r
  · refine Fin.cases (by norm_num [rowWeight,MacaulayFullBox.rowWeight,sourceWeight])
      (fun _=>ha) i
  · exact one_ne_zero

theorem trailing_degree_scale (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial ℝ))
    (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (d : Fin n→ℕ) (e W : ℕ) (a s : ℝ)
    (ha : a≠0) (hs : s≠0) (hA : RelativeProjectiveValueGram.polynomial H F d e W≠0) :
    (RelativeProjectiveValueGram.annihilator (fun i=>MvPolynomial.C (C a)*H i)
      (MvPolynomial.C (C s)*F) d e W).natTrailingDegree=
      (RelativeProjectiveValueGram.annihilator H F d e W).natTrailingDegree :=by
  change (X*(RelativeProjectiveValueGram.polynomial _ _ d e W).reflect _).natTrailingDegree=_
  rw [polynomial_scale]
  exact GramLeadingCoefficientCovariance.reflected_trailing_degree (matrix H F d e W)
    (rowWeight a W) s (rowWeight_ne_zero a ha W) hs hA
    (RelativeProjectiveValueGram.dimension n W) (RelativeProjectiveValueGram.degree_le H F d e W)

theorem trailing_zero_scale (H : Fin n→MvPolynomial (Fin (n+1)) (Polynomial ℝ))
    (F : MvPolynomial (Fin (n+1)) (Polynomial ℝ)) (d : Fin n→ℕ) (e W : ℕ) (a s : ℝ)
    (ha : a≠0) (hs : s≠0) (hA : RelativeProjectiveValueGram.polynomial H F d e W≠0) (t : ℝ) :
    (RelativeProjectiveValueGram.annihilator (fun i=>MvPolynomial.C (C a)*H i)
      (MvPolynomial.C (C s)*F) d e W).trailingCoeff.eval t=0 ↔
      (RelativeProjectiveValueGram.annihilator H F d e W).trailingCoeff.eval t=0 :=by
  change (X*(RelativeProjectiveValueGram.polynomial _ _ d e W).reflect _).trailingCoeff.eval t=0 ↔ _
  rw [polynomial_scale]
  exact GramLeadingCoefficientCovariance.reflected_trailing_zero_iff (matrix H F d e W)
    (rowWeight a W) s (rowWeight_ne_zero a ha W) hs hA
    (RelativeProjectiveValueGram.dimension n W) (RelativeProjectiveValueGram.degree_le H F d e W) t

end LeanCanny.Algebra.RelativeProjectiveValueScaling
