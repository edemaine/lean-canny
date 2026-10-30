/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointCells
public import LeanCanny.Algebra.IntegerPolynomialStationarySource
public import LeanCanny.Geometry.OrderedRealCellDerivativeSample
public import LeanCanny.Encoding.IntegerPolynomialSampleInput

/-! # Source-derived algebraic samples for refined endpoint gaps

The computed matching polynomial and its derivative supply candidates.
Derivative roots sample every bounded refined gap. Retaining the polynomial's
own roots also represents endpoint points when their neighboring fibers are
empty. Native adjacency rejects boundary candidates as interior samples.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointSamples
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open Geometry.OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def source (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : IntegerPolynomialRootQueriesBits.Source :=
  IntegerPolynomialStationaryBits.source (FlatAffineEndpointCells.source F hcone height)

theorem access {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.Access (source F hcone height) :=
  IntegerPolynomialStationaryBits.access (FlatAffineEndpointCells.access h hcone height hh)

noncomputable def roots (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → Finset ℝ :=
  IntegerPolynomialRootQueriesBits.rootSet (source F hcone height)

theorem countEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun r => BinaryNatCode.encode (roots F hcone height r).card) :=
  IntegerPolynomialRootQueriesBits.countEvaluator (access h hcone height hh)

theorem labelWidth_unary {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    UnaryFn (IntegerPolynomialRootQueriesBits.labelWidth (source F hcone height)) :=
  IntegerPolynomialRootQueriesBits.labelWidth_unary (access h hcone height hh)

theorem derivative_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    (FlatAffineEndpointExceptional.polynomial F height r).derivative ≠ 0 := by
  apply Polynomial.derivative_ne_zero.mpr
  exact (Polynomial.natDegree_pos_of_eval₂_root (FlatAffineEndpointExceptional.ne_zero F hcone height r hr a ha)
    (Int.castRingHom ℝ) (FlatAffineEndpointExceptional.retains_endpoint (SymbolicScaledSquarefree.scalarEvaluation a) F height r ha)
    (by intro z hz; change (z : ℝ) = 0 at hz; exact Int.cast_eq_zero.mp hz)).ne'

theorem source_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    (source F hcone height).polynomial r ≠ 0 :=
  mul_ne_zero (FlatAffineEndpointExceptional.ne_zero F hcone height r hr a ha)
    (derivative_ne_zero F hcone height r hr a ha)

theorem retains_endpoint (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    SymbolicScaledSquarefree.scalarEvaluation a ((source F hcone height).polynomial r) = 0 :=
  IntegerPolynomialStationaryBits.retains_root (FlatAffineEndpointCells.source F hcone height) r (Int.castRingHom ℝ) a
    (FlatAffineEndpointExceptional.retains_endpoint (SymbolicScaledSquarefree.scalarEvaluation a) F height r ha)

theorem mem_roots_iff (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) (t : ℝ) :
    t ∈ roots F hcone height r ↔ SymbolicScaledSquarefree.scalarEvaluation t
      ((source F hcone height).polynomial r) = 0 := by
  have hn : ((source F hcone height).polynomial r).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (source_ne_zero F hcone height r hr a ha)
  simp only [roots, IntegerPolynomialRootQueriesBits.rootSet,
    algebraMap_int_eq, Multiset.mem_toFinset, Polynomial.mem_roots hn,
    Polynomial.IsRoot, Polynomial.eval_map, SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom]

theorem exists_in_gap (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (k : Fin ((FlatAffineEndpointCells.roots F hcone height r).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointCells.roots F hcone height r).card) :
    ∃ t ∈ roots F hcone height r, t ∈ gap (FlatAffineEndpointCells.roots F hcone height r) k := by
  obtain ⟨t, ht, hp⟩ := exists_derivative_in_gap
    ((FlatAffineEndpointExceptional.polynomial F height r).map (Int.castRingHom ℝ))
    (FlatAffineEndpointCells.roots F hcone height r) (fun t ht => by
      rw [Polynomial.eval_map]
      exact (FlatAffineEndpointCells.mem_roots_iff F hcone height r hr a ha t).mp ht) k h0 hk
  refine ⟨t, (mem_roots_iff F hcone height r hr a ha t).mpr ?_, ht⟩
  apply IntegerPolynomialStationaryBits.retains_stationary
  simpa only [FlatAffineEndpointCells.source, Polynomial.derivative_map, Polynomial.eval_map,
    SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom] using hp

theorem in_gap_iff_stationary (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (k : Fin ((FlatAffineEndpointCells.roots F hcone height r).card + 1)) (t : ℝ)
    (ht : t ∈ gap (FlatAffineEndpointCells.roots F hcone height r) k) :
    t ∈ roots F hcone height r ↔ SymbolicScaledSquarefree.scalarEvaluation t
      (FlatAffineEndpointExceptional.polynomial F height r).derivative = 0 := by
  have hn := (FlatAffineEndpointCells.mem_roots_iff F hcone height r hr a ha t).not.mp (gap_no_root _ k ht)
  rw [mem_roots_iff F hcone height r hr a ha t]
  change SymbolicScaledSquarefree.scalarEvaluation t
    (FlatAffineEndpointExceptional.polynomial F height r * (FlatAffineEndpointExceptional.polynomial F height r).derivative) = 0 ↔ _
  rw [map_mul, mul_eq_zero, or_iff_right hn]

noncomputable def input (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : SquareSampleInput.Inputs :=
  IntegerPolynomialSampleInput.input (source F hcone height)

theorem sampleAccess {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    (input F hcone height).Access := IntegerPolynomialSampleInput.access (access h hcone height hh)

theorem vertex_mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SquareSampleCompleteVertices.language (input F hcone height) ∈ PSPACE :=
  IntegerPolynomialSampleInput.vertex_mem_PSPACE (access h hcone height hh)

theorem vertexWidth_unary {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    UnaryFn (SquareSampleCompleteVertices.width (input F hcone height)) :=
  IntegerPolynomialSampleInput.width_unary (access h hcone height hh)

theorem exists_label_in_gap (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    (a : ℝ) (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (k : Fin ((FlatAffineEndpointCells.roots F hcone height r).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointCells.roots F hcone height r).card) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (input F hcone height) r w,
      (SquareSampleCompleteVertices.candidate (input F hcone height) r w hw).val (0 : Fin 1) ∈
        gap (FlatAffineEndpointCells.roots F hcone height r) k := by
  obtain ⟨t, ht, hgap⟩ := exists_in_gap F hcone height r hr a ha k h0 hk
  obtain ⟨w, hw, he⟩ := IntegerPolynomialSampleInput.root_complete (source F hcone height) r
    (source_ne_zero F hcone height r hr a ha) t ((mem_roots_iff F hcone height r hr a ha t).mp ht)
  exact ⟨w, hw, he.symm ▸ hgap⟩

end LeanCanny.Encoding.FlatAffineEndpointSamples
