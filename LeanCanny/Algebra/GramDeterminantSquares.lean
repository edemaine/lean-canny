/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ProjectiveGramEliminant
/-! # A sum of squared minors for the actual rectangular Gram determinant

Summing over all row maps avoids choosing or ordering subsets. Each genuine
minor occurs once for every column permutation; repeated rows contribute zero.
The identity works over arbitrary commutative rings.
-/
@[expose] public section
namespace LeanCanny.Algebra.GramDeterminantSquares
open Matrix
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {R ι κ : Type*} [CommRing R] [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem expansion (A : Matrix ι κ R) :
    (A.transpose*A).det=∑f : κ→ι,(∏i,A (f i) i)*(A.submatrix f id).det :=by
  have HE:=(Matrix.detRowAlternating (R:=R) (n:=κ)).toMultilinearMap.map_sum
    (fun i r=>A r i • A r)
  change (Matrix.detRowAlternating (fun i=>∑r,A r i • A r))=_ at HE
  have HL : (fun i=>∑r,A r i • A r)=A.transpose*A:=by
    funext i j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.transpose_apply]
  rw [HL] at HE
  change (A.transpose*A).det=_ at HE
  refine HE.trans (Finset.sum_congr rfl (fun f _=>?_))
  exact (Matrix.detRowAlternating (R:=R) (n:=κ)).map_smul_univ (fun i=>A (f i) i) (fun i=>A (f i))

theorem factorial_mul (A : Matrix ι κ R) :
    (Fintype.card κ).factorial*(A.transpose*A).det=∑f : κ→ι,(A.submatrix f id).det^2 :=by
  have HE (σ : Equiv.Perm κ) :
      (∑f : κ→ι,(A.submatrix f id).det*((Equiv.Perm.sign σ:ℤ):R)*(∏i,A (f (σ i)) i))=
        (A.transpose*A).det:=by
    rw [expansion]
    let e : (κ→ι)≃(κ→ι):=
      { toFun:=fun f=>f∘σ
        invFun:=fun f=>f∘σ.symm
        left_inv:=fun f=>by funext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
        right_inv:=fun f=>by funext i; simp only [Function.comp_apply,Equiv.symm_apply_apply] }
    apply Fintype.sum_equiv e
    intro f
    have HD:=Matrix.det_permute σ (A.submatrix f id)
    change (A.submatrix (f∘σ) id).det=((Equiv.Perm.sign σ:ℤ):R)*(A.submatrix f id).det at HD
    rw [show e f=f∘σ from rfl,HD]
    simp only [Function.comp_apply]
    ring
  calc
    (Fintype.card κ).factorial*(A.transpose*A).det=
        ∑σ : Equiv.Perm κ,(A.transpose*A).det:=by simp only [Finset.sum_const,Finset.card_univ,
          Fintype.card_perm,nsmul_eq_mul]
    _=∑σ : Equiv.Perm κ,∑f : κ→ι,
        (A.submatrix f id).det*((Equiv.Perm.sign σ:ℤ):R)*(∏i,A (f (σ i)) i):=
      Finset.sum_congr rfl (fun σ _=>(HE σ).symm)
    _=∑f : κ→ι,(A.submatrix f id).det^2:=by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro f _
      simp only [mul_assoc]
      rw [←Finset.mul_sum]
      change (A.submatrix f id).det*
        (∑σ : Equiv.Perm κ,((Equiv.Perm.sign σ:ℤ):R)*∏i,(A.submatrix f id) (σ i) i)=_
      rw [←Matrix.det_apply']
      ring

end LeanCanny.Algebra.GramDeterminantSquares
