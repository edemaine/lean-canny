/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteSystemTransfer
public import LeanCanny.Algebra.IntegerCoordinatePolynomials

/-! # Representation bounds from a bound on the full solution set

Field embeddings preserve solution counts. A bound B on the full zero set
therefore bounds the parameter degree, coordinate degrees, and separating
direction of every representation. Integer clearing preserves these degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteSystemCoordinates
open Polynomial
open scoped Classical
variable {ι τ K L E : Type*} [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]

theorem ncard_le_of_embedding (p : τ → MvPolynomial ι K) (f : L →ₐ[K] E)
    (hf : (zeroSet (L := E) p).Finite) :
    (zeroSet (L := L) p).ncard ≤ (zeroSet (L := E) p).ncard := by
  apply Set.ncard_le_ncard_of_injOn (fun x j => f (x j)) ?_ ?_ hf
  · intro x hx j
    have hm := MvPolynomial.comp_aeval_apply (f := x) f (p j)
    exact hm.symm.trans ((congrArg f (hx j)).trans (map_zero f))
  · intro x _ y _ h
    funext j
    exact f.injective (congrFun h j)

namespace Representation
variable [Fintype ι] {p : τ → MvPolynomial ι K}
variable (r : Representation (L := L) p) (B : ℕ) (hB : (zeroSet (L := L) p).ncard ≤ B)

include hB

theorem polynomial_degree_le : r.polynomial.natDegree ≤ B := r.degree_eq.le.trans hB

theorem numerator_degree_le (j : ι) : (r.numerator j).natDegree ≤ B * B + 2 := by
  have hm := Nat.mul_le_mul ((Nat.sub_le (zeroSet (L := L) p).ncard 1).trans hB) hB
  have hd := r.numerator_degree j
  omega

theorem denominator_degree_le (j : ι) : (r.denominator j).natDegree ≤ B * B + 2 := by
  have hm := Nat.mul_le_mul ((Nat.sub_le (zeroSet (L := L) p).ncard 1).trans hB) hB
  have hd := r.denominator_degree j
  omega

theorem direction_le_of_ncard (j : ι) : r.direction j ≤ (Fintype.card ι + 1) * B ^ 4 :=
  (r.direction_le j).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB _))

end Representation
end LeanCanny.Algebra.FiniteSystemCoordinates
