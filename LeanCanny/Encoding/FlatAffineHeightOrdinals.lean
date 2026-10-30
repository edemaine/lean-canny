/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightCells
public import LeanCanny.Encoding.CoordinateBranchOrdinals

/-! # Short distinct-root records at every actual affine-height fiber

Positive coordinate leading coefficients keep the records injective even
at singular exceptional fibers. Along retained branches they stay constant.
The record width is derived from the original source's binary degree bound.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightOrdinals
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation MatrixPower Set
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def width (F : Inputs) (u : List Bool) : ℕ :=
  (FlatAffineHeightValues.coordinateDegree F u).size

theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (UnaryFn.length (FlatAffineHeightValues.coordinateDegree_binary h).bits_mem_FP).of_eq
    (fun _u => Nat.size_eq_bits_len _)

theorem coordinate_degree_bound (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u)) :
    (FlatAffineHeightGrid.coordinate F height u i).natDegree ≤ 2 ^ width F u := by
  apply (AffineShiftCoordinates.coordinate_degree_le _ _ _ i).trans
  apply Nat.le_trans ?_ (Nat.lt_size_self _).le
  exact (congrArg (fun n => n + 1) (FlatAffineHeightValues.dimension_eq F u)).symm.le

theorem specialized_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (t : ℝ) (i : Fin (count F u)) :
    (FlatAffineHeightGrid.coordinate F height u i).map (SymbolicScaledSquarefree.scalarEvaluation t) ≠ 0 := by
  have hl : SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineHeightGrid.coordinate F height u i).leadingCoeff ≠ 0 :=
    ne_of_gt (AffineShiftCoordinates.positive_leading (FlatAffinePowerPositive.system F u)
      (fun j => if j = height u then Polynomial.X else 0) (FlatAffinePowerPositive.degree F u)
      (FlatAffinePowerPositive.degree_pos F u) (FlatAffinePowerPositive.noInfinity F hcone u) i t)
  intro hz
  have H := congrArg Polynomial.leadingCoeff hz
  rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hl, Polynomial.leadingCoeff_zero] at H
  exact hl H

noncomputable def word (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (t : ℝ) (x : Fin (count F u) → ℝ) : List Bool :=
  CoordinateBranchOrdinals.word (width F u) (FlatAffineHeightGrid.coordinate F height u) t x

theorem word_length (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (t : ℝ) (x : Fin (count F u) → ℝ) :
    (word F height u t x).length = count F u * width F u :=
  CoordinateBranchOrdinals.length_word _ _ _ _

theorem length_unary {F : Inputs} (h : F.Access) : UnaryFn (fun u => count F u * width F u) :=
  (FlatAffineFullSourcePositive.count_unary h).mul (width_unary h)

theorem word_injective (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (t : ℝ)
    (x y : Fin (count F u) → ℝ)
    (hx : ∀ i, (FlatAffineHeightGrid.coordinate F height u i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) (x i) = 0)
    (hy : ∀ i, (FlatAffineHeightGrid.coordinate F height u i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) (y i) = 0)
    (he : word F height u t x = word F height u t y) : x = y :=
  CoordinateBranchOrdinals.word_injective_of_ne_zero _ _ _ (specialized_ne_zero F hcone height u t)
    (coordinate_degree_bound F height u) x y hx hy he

theorem coordinate_root (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (t : ℝ) (x : Fin (count F u) → ℝ)
    (hx : PolynomialGridValues.value (Connectivity.IntegerGridArcs.realRows
      (Connectivity.FlatAffineHeightArcs.rows F height u)) (t, x) = 0) (i : Fin (count F u)) :
    (FlatAffineHeightGrid.coordinate F height u i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t) (x i) = 0 := by
  have H := congrFun (AffineShiftCoordinates.capture (FlatAffinePowerPositive.system F u)
    (fun j => if j = height u then Polynomial.X else 0) (FlatAffinePowerPositive.degree F u)
    (FlatAffinePowerPositive.polynomial_degree F u) t x hx) i
  simpa only [SquarefreeRootFamily.value_apply, Pi.zero_apply, FlatAffineHeightGrid.coordinate] using H

theorem fiber_word_injective (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (t : ℝ) :
    Function.Injective (fun x : Connectivity.PolynomialGridArcs.Fiber
      (Connectivity.IntegerGridArcs.realRows (Connectivity.FlatAffineHeightArcs.rows F height u)) t =>
        word F height u t x.val) := by
  intro x y he
  apply Subtype.ext
  exact word_injective F hcone height u t x.val y.val
    (coordinate_root F height u t x.val x.property) (coordinate_root F height u t y.val y.property) he

theorem word_eq (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) {a b : ℝ}
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t
      (FlatAffineHeightSlabExceptional.polynomial F height u) ≠ 0)
    (f : C(Ioo a b, Fin (count F u) → ℝ))
    (hf : ∀ t i, (FlatAffineHeightGrid.coordinate F height u i).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation t.val) (f t i) = 0) (s t : Ioo a b) :
    word F height u s.val (f s) = word F height u t.val (f t) := by
  refine CoordinateBranchOrdinals.word_eq (width F u) (FlatAffineHeightGrid.coordinate F height u) ?_ f hf s t
  intro v hv i
  have H := FlatAffineHeightSlabExceptional.avoids (SymbolicScaledSquarefree.scalarEvaluation v)
    F hcone height u (havoid v hv)
  simp only [Connectivity.FlatAffineHeightArcs.exceptional, map_mul, map_prod, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] at H
  exact H.1 i

end LeanCanny.Encoding.FlatAffineHeightOrdinals
