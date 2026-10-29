/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerRows
public import LeanCanny.Algebra.ReciprocalCoordinateSpace
public import LeanCanny.Algebra.AffineCoordinateRowsSpace

/-! # Complete reciprocal homogeneous rows from original affine records -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerCoordinateRows
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def system (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    Fin (count F u + 1) → MvPolynomial (Fin (count F u + 1)) (Polynomial ℤ) :=
  AffineBoxGramEliminant.system
    (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F u) (FlatAffinePowerPositive.degree F u))
    (coordinate u).succ

lemma zero_row (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    system F coordinate u 0 = ReciprocalCoordinateBits.polynomial (count F) coordinate u := rfl

lemma tail_row (F : Inputs) (coordinate : (u : List Bool) → Fin (count F u)) (u : List Bool) (i : Fin (count F u)) :
    system F coordinate u i.succ =
      rename AffineCoordinateSystem.layout (WeightedHomogenization.homogenize (fun _ => 1)
        (FlatAffinePowerPositive.degree F u i) ((FlatAffinePowerPositive.system F u i).map Polynomial.C)) := by
  simp only [system, AffineBoxGramEliminant.system, Fin.cases_succ, AffineFiniteCoordinates.homogeneousRows,
    map_rename, WeightedHomogenization.map_homogenize]
  rfl

noncomputable def value (F : Inputs) (W : List Bool → ℕ)
    (coordinate : (u : List Bool) → Fin (count F u)) (row : (u : List Bool) → Fin (count F u + 1))
    (parameter modulus : List Bool → List Bool) (q : List Bool) : List Bool :=
  residueBits (((system F coordinate (pairFst q) (row (pairFst q))).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W (pairFst q)) (Nat.fromBitsLE (pairSnd q)))).coeff
      (Nat.fromBitsLE (parameter (pairFst q))) : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1))

theorem evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    (coordinate : (u : List Bool) → Fin (count F u)) (hc : UnaryFn (fun u => (coordinate u).val))
    (row : (u : List Bool) → Fin (count F u + 1)) (hr : UnaryFn (fun u => (row u).val))
    {parameter modulus : List Bool → List Bool} (hk : parameter ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value F W coordinate row parameter modulus) := by
  let tail := AffineCoordinateRowsBits.tailRow (count F) (FlatAffineFullSourcePositive.count_pos F) row
  have ht := AffineCoordinateRowsBits.tailRow_unary (FlatAffineFullSourcePositive.count_unary h)
    (FlatAffineFullSourcePositive.count_pos F) row hr
  have EL := ReciprocalCoordinateBits.evaluator (FlatAffineFullSourcePositive.count_unary h) hW coordinate hc hk hm
  have ER := FlatAffinePowerPositive.homogeneous_evaluator h hW tail ht hk hm
  have hz := FPPred.eq (hr.comp pairFst_mem_FP) (UnaryFn.const 0)
  refine (SpaceFunction.branch _ hz.flag_mem_FP EL ER).congr (funext fun q => ?_)
  simp only [decide_eq_true_eq]
  by_cases hi0 : (row (pairFst q)).val = 0
  · rw [ite_eq_left hi0]
    have hrow : row (pairFst q) = 0 := Fin.ext hi0
    unfold value
    rw [hrow, zero_row]
    rfl
  · rw [ite_eq_right hi0]
    unfold value
    rw [← AffineCoordinateRowsBits.tailRow_succ (count F) (FlatAffineFullSourcePositive.count_pos F) row (pairFst q) hi0]
    unfold system
    simp only [AffineBoxGramEliminant.system, Fin.cases_succ, AffineFiniteCoordinates.homogeneousRows,
      map_rename, WeightedHomogenization.map_homogenize]
    rfl

end LeanCanny.Encoding.FlatAffinePowerCoordinateRows
