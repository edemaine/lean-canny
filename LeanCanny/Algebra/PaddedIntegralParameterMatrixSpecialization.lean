/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PaddedIntegralParameterExtensionSpecialization
/-! # Actual padded-extension multiplication matrices under specialization

Both sides use the same advertised degree and padded rank. Relative-coordinate
transport proves naturality for every quotient element, including over
nonreduced coefficient rings and homomorphisms with kernel.
-/
@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open Polynomial
variable {A B :Type*} [CommRing A] [Nontrivial A] [CommRing B] [Nontrivial B]

theorem relative_matrix_specialize (φ :A→+*B) (p :A[X]) (d N :ℕ) (a :Extension p d N):
    (Algebra.leftMulMatrix (relativeBasis p d N) a).map φ=
      Algebra.leftMulMatrix (relativeBasis (p.map φ) d N) (specialize φ p d N a):=by
  ext i j
  rw [Matrix.map_apply,Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
    ←relativeBasis_repr_specialize φ p d N (a*relativeBasis p d N j) i,map_mul,specialize_relativeBasis]

theorem relative_charpoly_specialize (φ :A→+*B) (p :A[X]) (d N :ℕ) (a :Extension p d N):
    (Algebra.leftMulMatrix (relativeBasis (p.map φ) d N) (specialize φ p d N a)).charpoly=
      (Algebra.leftMulMatrix (relativeBasis p d N) a).charpoly.map φ:=by
  rw [←relative_matrix_specialize φ p d N a,Matrix.charpoly_map]

end LeanCanny.Algebra.PaddedIntegralParameterExtension
