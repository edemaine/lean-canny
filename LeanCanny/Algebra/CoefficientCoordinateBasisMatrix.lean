/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientCoordinateBasis
public import LeanCanny.Algebra.CoefficientCoordinateBasisSpecialization
public import LeanCanny.Algebra.MonicExtensionMatrix
/-! # Actual scalar-tower matrices over a retained coefficient ring -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientCoordinateBasis
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {R A :Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A] {m N :ℕ}

theorem tower_root_matrix {ι :Type*} [Fintype ι] [DecidableEq ι]
    (b :Module.Basis ι R A) (p :A[X]) (hp :p.Monic) (hd :p.natDegree=N) (i j :ι×Fin N):
    Algebra.leftMulMatrix (b.smulTower (relativeBasis p hp hd)) (AdjoinRoot.root p) i j=
      if j.2.val+1<N then (if i.2.val=j.2.val+1 then (if i.1=j.1 then 1 else 0) else 0)
      else -Algebra.leftMulMatrix b (p.coeff i.2.val) i.1 j.1:=by
  rw [Algebra.smulTower_leftMulMatrix,IntegralCoordinateBasis.relative_root_matrix]
  split_ifs <;> simp_all

theorem step_matrix (b :CoefficientCoordinateBasis R A m N) (p :A[X])
    (hp :p.Monic) (hd :p.natDegree=N) (a :AdjoinRoot p)
    (r s :Fin m→Fin N) (i j :Fin N):
    Algebra.leftMulMatrix (b.step p hp hd).basis a
      (indexEquiv m N (r,i)) (indexEquiv m N (s,j))=
      Algebra.leftMulMatrix (b.basis.smulTower (relativeBasis p hp hd)) a (r,i) (s,j):=by
  change Algebra.leftMulMatrix ((b.basis.smulTower (relativeBasis p hp hd)).reindex
    (indexEquiv m N)) a _ _=_
  simp only [Algebra.leftMulMatrix_eq_repr_mul,Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply,Equiv.symm_apply_apply]

theorem step_root_matrix (b :CoefficientCoordinateBasis R A m N) (p :A[X])
    (hp :p.Monic) (hd :p.natDegree=N) (r s :Fin m→Fin N) (i j :Fin N):
    Algebra.leftMulMatrix (b.step p hp hd).basis (AdjoinRoot.root p)
      (indexEquiv m N (r,i)) (indexEquiv m N (s,j))=
      if j.val+1<N then (if i.val=j.val+1 then (if r=s then 1 else 0) else 0)
      else -Algebra.leftMulMatrix b.basis (p.coeff i.val) r s:=by
  rw [step_matrix,tower_root_matrix]

theorem step_of_matrix (b :CoefficientCoordinateBasis R A m N) (p :A[X])
    (hp :p.Monic) (hd :p.natDegree=N) (a :A) (r s :Fin m→Fin N) (i j :Fin N):
    Algebra.leftMulMatrix (b.step p hp hd).basis (AdjoinRoot.of p a)
      (indexEquiv m N (r,i)) (indexEquiv m N (s,j))=
      if i=j then Algebra.leftMulMatrix b.basis a r s else 0:=by
  rw [step_matrix]
  change Algebra.leftMulMatrix (b.basis.smulTower (relativeBasis p hp hd))
    (algebraMap A (AdjoinRoot p) a) (r,i) (s,j)=_
  by_cases hi :i=j
  · subst j
    rw [ite_eq_left rfl]
    exact Algebra.smulTower_leftMulMatrix_algebraMap_eq b.basis (relativeBasis p hp hd) a r s i
  · rw [ite_eq_right hi]
    exact Algebra.smulTower_leftMulMatrix_algebraMap_ne b.basis (relativeBasis p hp hd) a r s hi

theorem padded_root_matrix (b :CoefficientCoordinateBasis R A m N) (p :A[X]) (d :ℕ)
    (r s :Fin m→Fin N) (i j :Fin N):
    Algebra.leftMulMatrix (b.paddedStep p d).basis (AdjoinRoot.root _)
      (indexEquiv m N (r,i)) (indexEquiv m N (s,j))=
      if j.val+1<N then (if i.val=j.val+1 then (if r=s then 1 else 0) else 0)
      else if (d ≤ N) ∧ (N - d ≤ i.val) then
        -(Algebra.leftMulMatrix b.basis (p.coeff (i.val-(N-d))) *
          Algebra.leftMulMatrix b.basis (p.coeff d)^(d-1-(i.val-(N-d)))) r s
      else 0:=by
  change Algebra.leftMulMatrix (b.step _ _ _).basis _ _ _=_
  rw [step_root_matrix]
  by_cases hj :j.val+1<N
  · rw [ite_eq_left hj,ite_eq_left hj]
  · rw [ite_eq_right hj,ite_eq_right hj,PaddedIntegralNormalization.coefficient_below]
    by_cases hi :(d ≤ N) ∧ (N - d ≤ i.val)
    · rw [ite_eq_left hi,ite_eq_left hi,map_mul,map_pow]
    · rw [ite_eq_right hi,ite_eq_right hi,map_zero]
      simp

omit [Nontrivial A] in
theorem Specializes.matrix_map {S B :Type*} [CommRing S] [CommRing B] [Algebra S B]
    {φ :R→+*S} {ψ :A→+*B} {b :CoefficientCoordinateBasis R A m N}
    {c :CoefficientCoordinateBasis S B m N} (H :Specializes φ ψ b c) (a :A):
    (Algebra.leftMulMatrix b.basis a).map φ=Algebra.leftMulMatrix c.basis (ψ a):=by
  ext i j
  rw [Matrix.map_apply,Algebra.leftMulMatrix_eq_repr_mul,Algebra.leftMulMatrix_eq_repr_mul,
    ←H.coordinates (a*b.basis j) i,map_mul,H.basis]

omit [Nontrivial A] in
theorem Specializes.charpoly_map {S B :Type*} [CommRing S] [CommRing B] [Algebra S B]
    {φ :R→+*S} {ψ :A→+*B} {b :CoefficientCoordinateBasis R A m N}
    {c :CoefficientCoordinateBasis S B m N} (H :Specializes φ ψ b c) (a :A):
    (Algebra.leftMulMatrix c.basis (ψ a)).charpoly=
      (Algebra.leftMulMatrix b.basis a).charpoly.map φ:=by
  rw [←H.matrix_map a,Matrix.charpoly_map]

end LeanCanny.Algebra.CoefficientCoordinateBasis
