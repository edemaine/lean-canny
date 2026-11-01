/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCoordinateTrailing

/-! # Original-spatial ceilings for relative coordinate trailing cuts

One ambient spatial degree/arity controls every later free-block sweep.
The outer coordinate degree and the sweep-parameter coefficient degree are
binary metadata computed without old algebra ranks or norm degrees.
These ceilings are inputs to the one initial cap; no current prefix is resized.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSweepBounds
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical

def coordinateCap (a D : ℕ) := PurePowerReductionBounds.dimension a D
def parameterCap (a D : ℕ) := coordinateCap a D * ((PurePowerReductionBounds.bound a D + 1) * D)

theorem parameterCap_binary {a D : List Bool → ℕ} (ha : UnaryFn a) (hD : BinaryFn D) :
    BinaryFn (fun q => parameterCap (a q) (D q)) :=
  (PurePowerReductionBounds.dimension_binary ha hD).mul
    (((PurePowerReductionBounds.bound_binary (BinaryFn.ofUnary ha) hD).add (BinaryFn.const 1)).mul hD)

theorem parameterDegree_le {n : ℕ} (D : ℕ) (r : Rule n) : parameterDegree D r ≤ parameterCap (n + 1) D := by
  have HA : n - r.critical.offset.val + 1 ≤ n + 1 := by omega
  have HK := IntegralCriticalFactorCeiling.dimension_mono HA (Nat.le_refl D)
  have HB : PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) D ≤ PurePowerReductionBounds.bound (n + 1) D :=
    Nat.add_le_add_right (Nat.mul_le_mul_right (D - 1) HA) 1
  exact Nat.mul_le_mul HK (Nat.mul_le_mul_right D (Nat.add_le_add_right HB 1))

theorem factor_degree {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (IntegralMixedCoordinateTrailing.ChoiceBound P r)) :
    (IntegralMixedCoordinateTrailing.factor x hm r j i).natDegree ≤ parameterCap (n + 1) P.degree :=
  (IntegralMixedCoordinateTrailing.factor_degree x hm r j i).trans (parameterDegree_le P.degree r)

theorem nilpotent_coefficient_cap {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (k N : ℕ) (hN : parameterCap (n + 1) P.degree < N) :
    ((coordinate x hm r j).coeff k).natDegree < N :=
  ((coordinate_coefficient_degree x hm r j k).trans (parameterDegree_le P.degree r)).trans_lt hN

end LeanCanny.Algebra.IntegralMixedSweepBounds
