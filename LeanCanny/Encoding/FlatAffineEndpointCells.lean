/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointExceptional

/-! # Native parameter cells for endpoint matching

The refined polynomial retains every original endpoint height. Its native
root counts and rational cell queries locate intervals where all computed
midpoint signs are stable. `FlatAffineEndpointCheckedIncidence` supplies
native algebraic adjacent-sample matching on complete joint labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointCells
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open Geometry.OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def source (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := FlatAffineEndpointExceptional.polynomial F height
  degree := FlatAffineEndpointExceptional.degreeBound F
  mass := FlatAffineEndpointExceptional.massBound F
  degree_bound := FlatAffineEndpointExceptional.degree_le F hcone height
  mass_bound := FlatAffineEndpointExceptional.mass_le F height

theorem access {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.Access (source F hcone height) :=
  ⟨FlatAffineEndpointExceptional.evaluator h height hh, FlatAffineEndpointExceptional.degreeBound_binary h height,
    FlatAffineEndpointExceptional.massBound_binary h height⟩

noncomputable def roots (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → Finset ℝ :=
  IntegerPolynomialRootQueriesBits.rootSet (source F hcone height)

theorem countEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun r => BinaryNatCode.encode (roots F hcone height r).card) :=
  IntegerPolynomialRootQueriesBits.countEvaluator (access h hcone height hh)

theorem cellEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun q => BinaryNatCode.encode (IntegerPolynomialRootQueriesBits.cellCode (source F hcone height) q)) :=
  IntegerPolynomialRootQueriesBits.cellEvaluator (access h hcone height hh)

theorem cell_mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.cellLanguage (source F hcone height) ∈ PSPACE :=
  IntegerPolynomialRootQueriesBits.cell_mem_PSPACE (access h hcone height hh)

theorem mem_roots_iff (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) (t : ℝ) :
    t ∈ roots F hcone height r ↔ SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineEndpointExceptional.polynomial F height r) = 0 := by
  have hn : (FlatAffineEndpointExceptional.polynomial F height r).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (FlatAffineEndpointExceptional.ne_zero F hcone height r hr a ha)
  simp only [roots, IntegerPolynomialRootQueriesBits.rootSet, source, algebraMap_int_eq,
    Multiset.mem_toFinset, Polynomial.mem_roots hn, Polynomial.IsRoot, Polynomial.eval_map,
    SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom]

theorem endpoint_mem (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) : a ∈ roots F hcone height r := by
  apply (mem_roots_iff F hcone height r hr a ha a).mpr
  exact FlatAffineEndpointExceptional.retains_endpoint (SymbolicScaledSquarefree.scalarEvaluation a) F height r ha

theorem gap_avoids (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (k : Fin ((roots F hcone height r).card + 1)) (t : ℝ) (ht : t ∈ gap (roots F hcone height r) k)
    (i : Fin (count F (pairFst r))) :
    SymbolicScaledSquarefree.scalarEvaluation t (Geometry.FlatAffineEndpointMidpoint.testPolynomial F height r i).trailingCoeff ≠ 0 := by
  apply FlatAffineEndpointExceptional.avoids _ F height r ?_ i
  exact (mem_roots_iff F hcone height r hr a ha t).not.mp (gap_no_root _ k ht)

theorem gap_avoids_original (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (k : Fin ((roots F hcone height r).card + 1)) (t : ℝ) (ht : t ∈ gap (roots F hcone height r) k) :
    SymbolicScaledSquarefree.scalarEvaluation t (Connectivity.FlatAffineHeightArcs.exceptional F height (pairFst r)) ≠ 0 := by
  have H := (mem_roots_iff F hcone height r hr a ha t).not.mp (gap_no_root _ k ht)
  have HE := (mul_ne_zero_iff.mp (by simpa only [FlatAffineEndpointExceptional.polynomial, map_mul] using H)).1
  exact FlatAffineHeightSlabExceptional.avoids _ F hcone height (pairFst r) HE

end LeanCanny.Encoding.FlatAffineEndpointCells
