/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasisFin
public import LeanCanny.Algebra.MonicExtensionMatrix

/-! # Exact fixed-width companion layout for a new scalar head

The new scalar occupies the least significant basis digit. Old basis ranks
and the new power index therefore combine by the ordinary finite-product
equivalence. This identifies the actual canonical basis with the companion
matrix basis, without an extra permutation table.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateBasis
open FixedWidthPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def pairIndex (m B : ℕ) : (Fin (count m B) × Fin (2 ^ B)) ≃ Fin (count (m + 1) B) :=
  finProdFinEquiv.trans (finCongr (by unfold count; rw [pow_succ]))

theorem box_head (m B : ℕ) (e : Fin m → Fin (2 ^ B)) (j : Fin (2 ^ B)) :
    boxEquiv (m + 1) B (Fin.cons j e) = pairIndex m B (boxEquiv m B e, j) := by
  apply Fin.ext
  change (finFunctionFinEquiv (Fin.cons j e) : ℕ) = j.val + 2 ^ B * (finFunctionFinEquiv e).val
  rw [finFunctionFinEquiv_apply, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one]
  rw [finFunctionFinEquiv_apply, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_succ]
  ring

variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

theorem finBasis_step (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A)
    (hp : p.Monic) (hd : p.natDegree = 2 ^ B) (r : Fin (count m B)) (j : Fin (2 ^ B)) :
    (b.step p hp hd).finBasis (pairIndex m B (r, j)) =
      (b.finBasis.smulTower (relativeBasis p hp hd)) (r, j) := by
  rw [finBasis, Module.Basis.reindex_apply]
  have HE : (boxEquiv (m + 1) B).symm (pairIndex m B (r, j)) =
      Fin.cons j ((boxEquiv m B).symm r) := by
    apply (boxEquiv (m + 1) B).injective
    rw [Equiv.apply_symm_apply, box_head, Equiv.apply_symm_apply]
  rw [HE]
  rw [step, Module.Basis.reindex_apply, Module.Basis.smulTower_apply]
  change b.basis ((boxEquiv m B).symm r) • relativeBasis p hp hd j = _
  rw [Module.Basis.smulTower_apply, finBasis, Module.Basis.reindex_apply]

theorem finBasis_step_eq (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A)
    (hp : p.Monic) (hd : p.natDegree = 2 ^ B) :
    (b.step p hp hd).finBasis =
      (b.finBasis.smulTower (relativeBasis p hp hd)).reindex (pairIndex m B) := by
  ext i
  obtain ⟨⟨r, j⟩, rfl⟩ := (pairIndex m B).surjective i
  rw [Module.Basis.reindex_apply, Equiv.symm_apply_apply, finBasis_step]

theorem finBasis_step_matrix (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A)
    (hp : p.Monic) (hd : p.natDegree = 2 ^ B) (x : AdjoinRoot p)
    (r t : Fin (count m B)) (i j : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (b.step p hp hd).finBasis x
      (pairIndex m B (r, i)) (pairIndex m B (t, j)) =
      Algebra.leftMulMatrix (b.finBasis.smulTower (relativeBasis p hp hd)) x (r, i) (t, j) := by
  rw [finBasis_step_eq]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.repr_reindex_apply,
    Module.Basis.reindex_apply, Equiv.symm_apply_apply]

theorem finBasis_root_matrix (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A)
    (hp : p.Monic) (hd : p.natDegree = 2 ^ B)
    (r t : Fin (count m B)) (i j : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (b.step p hp hd).finBasis (AdjoinRoot.root p)
      (pairIndex m B (r, i)) (pairIndex m B (t, j)) =
      if j.val + 1 < 2 ^ B then (if i.val = j.val + 1 then (if r = t then 1 else 0) else 0)
      else -Algebra.leftMulMatrix b.finBasis (p.coeff i.val) r t := by
  rw [finBasis_step_matrix, tower_root_matrix]

theorem finBasis_of_matrix (b : IntegralCoordinateBasis A m (2 ^ B)) (p : Polynomial A)
    (hp : p.Monic) (hd : p.natDegree = 2 ^ B) (x : A)
    (r t : Fin (count m B)) (i j : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (b.step p hp hd).finBasis (AdjoinRoot.of p x)
      (pairIndex m B (r, i)) (pairIndex m B (t, j)) =
      if i = j then Algebra.leftMulMatrix b.finBasis x r t else 0 := by
  rw [finBasis_step_matrix]
  change Algebra.leftMulMatrix (b.finBasis.smulTower (relativeBasis p hp hd))
    (algebraMap A (AdjoinRoot p) x) (r, i) (t, j) = _
  by_cases hi : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact Algebra.smulTower_leftMulMatrix_algebraMap_eq b.finBasis (relativeBasis p hp hd) x r t i
  · rw [ite_eq_right hi]
    exact Algebra.smulTower_leftMulMatrix_algebraMap_ne b.finBasis (relativeBasis p hp hd) x r t hi

end LeanCanny.Algebra.IntegralCoordinateBasis
