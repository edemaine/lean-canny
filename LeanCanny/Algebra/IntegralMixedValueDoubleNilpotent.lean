/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueMatrixSource
public import LeanCanny.Algebra.IntegralNilpotentMatrix

/-! # Two formal digits recover the actual value/Gram coefficient

The first nilpotent digit stores the sweep parameter. A second stores the
reciprocal value variable of the actual Gram determinant. Both use the
same initial original-spatial cap; neither is a physical history birth.
High terms vanish without wrapping. Two zero-column matrix selections
recover the requested literal old-bank coefficient.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueDoubleNilpotent
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedCoordinateSquarefree
open IntegralMixedExceptionalBounds IntegralCoordinateBasis FixedWidthPolynomial Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev First (x : State P S B m ι) := AdjoinRoot (X ^ (2 ^ B) : Polynomial x.sampler.scalarPrefix.carrier)
abbrev Second (x : State P S B m ι) := AdjoinRoot (X ^ (2 ^ B) : Polynomial (First x))

theorem first_nontrivial (x : State P S B m ι) : Nontrivial (First x) :=
  nontrivial_of_ne _ _ ((IntegralMixedCutNilpotent.basis x).finBasis.ne_zero (zeroFin (m + 1) B))

noncomputable def basis (x : State P S B m ι) : Module.Basis (Fin (count (m + 2) B)) ℤ (Second x) := by
  let := first_nontrivial x
  exact ((IntegralMixedCutNilpotent.basis x).finBasis.smulTower
    (relativeBasis (X ^ (2 ^ B)) (monic_X_pow _) (natDegree_X_pow _))).reindex (pairIndex (m + 1) B)

theorem basis_matrix (x : State P S B m ι) (f : Polynomial (First x))
    (u v : Fin (count (m + 1) B)) (e h : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (basis x) (AdjoinRoot.mk (X ^ (2 ^ B)) f)
      (pairIndex (m + 1) B (u, e)) (pairIndex (m + 1) B (v, h)) =
      if h.val ≤ e.val then Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
        (f.coeff (e.val - h.val)) u v else 0 := by
  let := first_nontrivial x
  unfold basis
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  simp only [Module.Basis.repr_reindex_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  have H := IntegralNilpotentMatrix.tower (IntegralMixedCutNilpotent.basis x).finBasis (2 ^ B) f u v e h
  rw [Algebra.leftMulMatrix_eq_repr_mul] at H
  exact H

noncomputable def matrix (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :=
  (IntegralMixedValueMatrixSource.nilpotentMatrix x hm r i).map (AdjoinRoot.mk (X ^ (2 ^ B)))

theorem matrix_det (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) :
    (matrix x hm r i).det = AdjoinRoot.mk (X ^ (2 ^ B))
      (IntegralMixedValueMatrixSource.nilpotentMatrix x hm r i).det :=
  (RingHom.map_det (AdjoinRoot.mk (X ^ (2 ^ B))) _).symm

theorem dimension_lt (P : SpatialSource n) (r : Rule n) :
    IntegralMixedGridValue.dimension P r < auxiliaryCap (n + 1) P.degree := by
  have HD := IntegralMixedExceptionalBounds.value_dimension_le P r
  have HC : valueDimension (n + 1) P.degree ≤ valueCap (n + 1) P.degree := by
    have HP := P.degree_two
    unfold valueCap
    exact (Nat.mul_one _).symm.trans_le (Nat.mul_le_mul_left _ (by omega))
  unfold auxiliaryCap
  omega

def reflectedIndex (P : SpatialSource n) (r : Rule n)
    (k : Fin (IntegralMixedValueTrailing.ChoiceBound P r)) : ℕ :=
  IntegralMixedGridValue.dimension P r - (k.val - 1)

theorem reflectedIndex_lt (P : SpatialSource n) (r : Rule n)
    (k : Fin (IntegralMixedValueTrailing.ChoiceBound P r))
    (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B) : reflectedIndex P r k < 2 ^ B :=
  (Nat.sub_le _ _).trans_lt ((dimension_lt P r).trans_le hcap)

theorem determinant_entry_succ (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : ℕ) (hk : k ≤ IntegralMixedGridValue.dimension P r)
    (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B) (u v : Fin (count (m + 1) B)) :
    Algebra.leftMulMatrix (basis x) (matrix x hm r i).det
      (pairIndex (m + 1) B (u, ⟨IntegralMixedGridValue.dimension P r - k,
        (Nat.sub_le _ _).trans_lt ((dimension_lt P r).trans_le hcap)⟩))
      (pairIndex (m + 1) B (v, 0)) =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
        (IntegralMixedCutNilpotent.value x hm r (.value i ⟨k + 1, by
          change k + 1 < IntegralMixedGridValue.dimension P r + 2; omega⟩)) u v := by
  let := first_nontrivial x
  rw [matrix_det]
  rw [IntegralMixedValueMatrixSource.nilpotent_value_succ x hm r i k hk, basis_matrix]
  simp only [Fin.val_zero, Nat.zero_le, ite_true, Nat.sub_zero]


theorem determinant_entry (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : Fin (IntegralMixedValueTrailing.ChoiceBound P r))
    (hk : 0 < k.val) (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (u v : Fin (count (m + 1) B)) :
    Algebra.leftMulMatrix (basis x) (matrix x hm r i).det
      (pairIndex (m + 1) B (u, ⟨reflectedIndex P r k, reflectedIndex_lt P r k hcap⟩))
      (pairIndex (m + 1) B (v, 0)) =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis x).finBasis
        (IntegralMixedCutNilpotent.value x hm r (.value i k)) u v := by
  have Hk : k.val - 1 ≤ IntegralMixedGridValue.dimension P r := by have H := k.isLt; change k.val < _ + 2 at H; omega
  have H := determinant_entry_succ x hm r i (k.val - 1) Hk hcap u v
  have HE : (⟨k.val - 1 + 1, by change k.val - 1 + 1 < IntegralMixedGridValue.dimension P r + 2; omega⟩ :
      Fin (IntegralMixedValueTrailing.ChoiceBound P r)) = k := Fin.ext (Nat.sub_add_cancel hk)
  rw [HE] at H
  exact H

theorem raw_coefficient (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (i : Fin (n - r.critical.offset.val + 1)) (k : Fin (IntegralMixedValueTrailing.ChoiceBound P r))
    (hk : 0 < k.val) (hcap : auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (e : Fin (2 ^ B)) (u v : Fin (count m B)) :
    Algebra.leftMulMatrix (basis x) (matrix x hm r i).det
      (pairIndex (m + 1) B (pairIndex m B (u, e),
        ⟨reflectedIndex P r k, reflectedIndex_lt P r k hcap⟩))
      (pairIndex (m + 1) B (pairIndex m B (v, 0), 0)) =
      IntegralMixedCutMatrix.coefficientMatrix x hm r (.value i k) e.val u v := by
  rw [determinant_entry x hm r i k hk hcap]
  exact IntegralMixedCutNilpotent.coefficient x hm r (.value i k) hcap e u v

theorem rank_cap (hm : m ≤ S) : count (m + 2) B ≤ count (S + 2) B :=
  Nat.pow_le_pow_right (Nat.two_pow_pos B) (by omega)

theorem rank_bits (hm : m ≤ S) : (count (m + 2) B).size ≤ B * (S + 2) + 1 := by
  unfold count
  rw [← pow_mul, Nat.size_pow]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left B (by omega)) 1

end LeanCanny.Algebra.IntegralMixedValueDoubleNilpotent
