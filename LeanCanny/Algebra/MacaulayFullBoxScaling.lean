/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MacaulayFullBox
/-! # Row scaling commutes with the actual full Macaulay matrix

Source rows acquire their polynomial's weight. The identity padding rows
have weight one. A coefficient hom preserves these same fixed row/column
boxes, including every incompatible zero row.
-/
@[expose] public section
namespace LeanCanny.Algebra.MacaulayFullBox
open MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n W : ℕ} {R S : Type*} [CommRing R] [CommRing S]

def rowWeight (w : Fin n→R) : Row n W→R
  | .inl (i,_)=>w i
  | .inr _=>1

theorem matrix_scale (p : Fin n→MvPolynomial (Fin n) R) (d : Fin n→ℕ) (W : ℕ) (w : Fin n→R) :
    matrix (fun i=>C (w i)*p i) d W=
      fun a b=>rowWeight w a*matrix p d W a b :=by
  funext a b
  rcases a with ⟨i,a⟩|a
  · change (if _ then _ else 0)=w i*(if _ then _ else 0)
    split_ifs
    · rw [←mul_assoc,mul_comm (monomial _ 1),mul_assoc,MvPolynomial.coeff_C_mul]
    · exact (mul_zero _).symm
  · simp only [matrix,rowWeight,one_mul]

theorem matrix_scale_map (p : Fin n→MvPolynomial (Fin n) R) (d : Fin n→ℕ) (W : ℕ)
    (φ : R→+*S) (w : Fin n→S) :
    matrix (fun i=>C (w i)*(p i).map φ) d W=
      fun a b=>rowWeight w a*(matrix p d W).map φ a b :=by
  rw [matrix_scale,←matrix_map]

end LeanCanny.Algebra.MacaulayFullBox
