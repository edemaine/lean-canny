/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralParameterExtensionMatrix
public import LeanCanny.Algebra.IntegralParameterExtensionSpecialization
/-! # Specialization of actual scalar-extension generator matrices

The matrix is constructed from the advertised-degree normalization on each
side. Its specialization requires no surviving coefficient or matrix receipt.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterExtension
open Polynomial
open scoped Classical
variable {A B :Type*} [CommRing A] [Nontrivial A] [CommRing B] [Nontrivial B]

theorem relative_root_matrix_map (φ :A→+*B) (p :A[X]) (d :ℕ):
    (Algebra.leftMulMatrix (relativeBasis p d) (AdjoinRoot.root _)).map φ=
      Algebra.leftMulMatrix (relativeBasis (p.map φ) d) (AdjoinRoot.root _):=by
  ext i j
  simp only [Matrix.map_apply,root_matrix]
  split_ifs <;> simp only [map_zero,map_one,map_neg,map_mul,map_pow,coeff_map]

theorem relative_root_charpoly_map (φ :A→+*B) (p :A[X]) (d :ℕ):
    (Algebra.leftMulMatrix (relativeBasis (p.map φ) d) (AdjoinRoot.root _)).charpoly=
      (Algebra.leftMulMatrix (relativeBasis p d) (AdjoinRoot.root _)).charpoly.map φ:=by
  rw [←relative_root_matrix_map φ p d,Matrix.charpoly_map]

theorem relative_mk_matrix_map (φ :A→+*B) (p q :A[X]) (d :ℕ):
    (Algebra.leftMulMatrix (relativeBasis p d)
      (AdjoinRoot.mk (FixedDegreeIntegralNormalization.polynomial p d) q)).map φ=
    Algebra.leftMulMatrix (relativeBasis (p.map φ) d)
      (AdjoinRoot.mk (FixedDegreeIntegralNormalization.polynomial (p.map φ) d) (q.map φ)):=by
  let left :A[X]→+*Matrix (Fin d) (Fin d) B:=φ.mapMatrix.comp
    ((Algebra.leftMulMatrix (relativeBasis p d)).toRingHom.comp (AdjoinRoot.mk _))
  let right :A[X]→+*Matrix (Fin d) (Fin d) B:=
    ((Algebra.leftMulMatrix (relativeBasis (p.map φ) d)).toRingHom.comp
      (AdjoinRoot.mk _)).comp (Polynomial.mapRingHom φ)
  have HE:left=right:=by
    apply Polynomial.ringHom_ext
    · intro a
      change (Algebra.leftMulMatrix (relativeBasis p d) (AdjoinRoot.mk _ (C a))).map φ=
        Algebra.leftMulMatrix (relativeBasis (p.map φ) d) (AdjoinRoot.mk _ ((C a).map φ))
      rw [Polynomial.map_C,AdjoinRoot.mk_C,AdjoinRoot.mk_C]
      change (Algebra.leftMulMatrix (relativeBasis p d) (algebraMap A _ a)).map φ=
        Algebra.leftMulMatrix (relativeBasis (p.map φ) d) (algebraMap B _ (φ a))
      rw [AlgHom.commutes,AlgHom.commutes]
      ext i j
      simp only [Matrix.map_apply,Matrix.algebraMap_matrix_apply,Algebra.algebraMap_self]
      split_ifs <;> first | rfl | exact map_zero φ
    · change (Algebra.leftMulMatrix (relativeBasis p d) (AdjoinRoot.root _)).map φ=
        Algebra.leftMulMatrix (relativeBasis (p.map φ) d)
          (AdjoinRoot.mk _ (Polynomial.map φ X))
      rw [Polynomial.map_X,AdjoinRoot.mk_X]
      exact relative_root_matrix_map φ p d
  exact RingHom.congr_fun HE q

theorem relative_mk_charpoly_map (φ :A→+*B) (p q :A[X]) (d :ℕ):
    (Algebra.leftMulMatrix (relativeBasis (p.map φ) d)
      (AdjoinRoot.mk (FixedDegreeIntegralNormalization.polynomial (p.map φ) d) (q.map φ))).charpoly=
    (Algebra.leftMulMatrix (relativeBasis p d)
      (AdjoinRoot.mk (FixedDegreeIntegralNormalization.polynomial p d) q)).charpoly.map φ:=by
  rw [←relative_mk_matrix_map φ p q d,Matrix.charpoly_map]

theorem relative_matrix_specialize (φ :A→+*B) (p :A[X]) (d :ℕ) (a :Extension p d):
    (Algebra.leftMulMatrix (relativeBasis p d) a).map φ=
      Algebra.leftMulMatrix (relativeBasis (p.map φ) d) (specialize φ p d a):=by
  ext i j
  rw [Matrix.map_apply,Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
    ←relativeBasis_repr_specialize φ p d (a*relativeBasis p d j) i,map_mul,specialize_relativeBasis]

theorem relative_charpoly_specialize (φ :A→+*B) (p :A[X]) (d :ℕ) (a :Extension p d):
    (Algebra.leftMulMatrix (relativeBasis (p.map φ) d) (specialize φ p d a)).charpoly=
      (Algebra.leftMulMatrix (relativeBasis p d) a).charpoly.map φ:=by
  rw [←relative_matrix_specialize φ p d a,Matrix.charpoly_map]

end LeanCanny.Algebra.IntegralParameterExtension
