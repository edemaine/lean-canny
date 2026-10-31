/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralSelectedMatrixSource
public import LeanCanny.Algebra.PaddedIntegralHeightMatrix

/-! # Actual height matrices attached to the original scalar-prefix source

The numerator multiplication matrix is the constructed new generator times
the lifted selected inverse matrix. The nonzero characteristic denominator
uses the same original coefficient matrix in its fixed-width basis.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralHeightSourceMatrix
open PaddedIntegralGeneratorSource IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def liftMatrix (S : Source) (c : List Bool) :
    Matrix (Fin (count (S.arity c + 1) (S.width c))) (Fin (count (S.arity c + 1) (S.width c))) ℤ := fun r t =>
  let u := (pairIndex (S.arity c) (S.width c)).symm r
  let v := (pairIndex (S.arity c) (S.width c)).symm t
  if u.2 = v.2 then PaddedIntegralSelectedMatrixSource.matrix S c u.1 v.1 else 0

noncomputable def matrix (S : Source) (c : List Bool) :
    Matrix (Fin (count (S.arity c + 1) (S.width c))) (Fin (count (S.arity c + 1) (S.width c))) ℤ := by
  letI := S.ring c
  letI := S.nontrivial c
  exact Algebra.leftMulMatrix
    (PaddedIntegralParameterExtension.coordinateBasis (S.basis c) (S.polynomial c) (S.degree c)).finBasis
    (PaddedIntegralParameterExtension.numerator (S.basis c) (S.polynomial c) (S.degree c))

theorem matrix_eq (S : Source) (c : List Bool) : matrix S c = S.matrix c * liftMatrix S c := by
  let := S.ring c
  let := S.nontrivial c
  change Algebra.leftMulMatrix _ (PaddedIntegralParameterExtension.numerator _ _ _) = _
  rw [PaddedIntegralParameterExtension.numerator_matrix]
  congr 1
  ext r t
  obtain ⟨⟨u, i⟩, rfl⟩ := (pairIndex (S.arity c) (S.width c)).surjective r
  obtain ⟨⟨v, j⟩, rfl⟩ := (pairIndex (S.arity c) (S.width c)).surjective t
  rw [PaddedIntegralParameterExtension.lifted_inverse_entry]
  simp only [liftMatrix, Equiv.symm_apply_apply]
  rfl

noncomputable def denominator (S : Source) (c : List Bool) : ℤ :=
  IntegralParameterInverse.denominator (S.coefficient c (S.degree c)).charpoly

theorem denominator_ne_zero (S : Source) (c : List Bool) : denominator S c ≠ 0 :=
  IntegralParameterInverse.denominator_ne_zero _ (Matrix.charpoly_monic _).ne_zero

theorem denominator_eq (S : Source) (c : List Bool) :
    letI := S.ring c
    letI := S.nontrivial c
    denominator S c = PaddedIntegralParameterExtension.denominator (S.basis c) (S.polynomial c) (S.degree c) := by
  let := S.ring c
  let := S.nontrivial c
  exact (PaddedIntegralParameterExtension.denominator_finBasis _ _ _).symm

theorem denominator_value (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (q : List Bool) :
    PaddedIntegralSelectedMatrixSource.denominatorValue S B q =
      MatrixPower.residueBits ((denominator S (base q) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  change IntegralParameterInverseBits.denominatorValue (PaddedIntegralSelectedMatrixSource.integerFamily S B)
    (LeanCanny.pair q (modulus q)) = _
  generalize hm : modulus q = mw
  generalize hz : LeanCanny.pair q mw = r
  have hq : LeanCanny.pairFst r = q := by rw [← hz, LeanCanny.pairFst_pair]
  have hw : LeanCanny.pairSnd r = mw := by rw [← hz, LeanCanny.pairSnd_pair]
  subst q
  subst mw
  rfl

end LeanCanny.Algebra.PaddedIntegralHeightSourceMatrix
