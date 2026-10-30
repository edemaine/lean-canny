/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightSlabExceptional
public import LeanCanny.Algebra.IntegerPolynomialRootQueriesSpace

/-! # Native ordered parameter cells of the actual affine-height system

The computed complete exceptional polynomial supplies the cells. Rational
root counts and point-or-gap codes retain all original coefficient calls.
Every gap avoids the exact exceptional factors required by the arc theorem.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightCells
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open Geometry.OrderedRealCells
open scoped Classical
set_option maxHeartbeats 300000

noncomputable def source (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : IntegerPolynomialRootQueriesBits.Source where
  polynomial := FlatAffineHeightSlabExceptional.polynomial F height
  degree := FlatAffineHeightSlabExceptional.degreeBound F
  mass := FlatAffineHeightSlabExceptional.massBound F
  degree_bound := FlatAffineHeightSlabExceptional.degree_bound F hcone height
  mass_bound := FlatAffineHeightSlabExceptional.mass_bound F height

theorem access {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.Access (source F hcone height) :=
  ⟨FlatAffineHeightSlabExceptional.evaluator h height hh,
    FlatAffineHeightSlabExceptional.degreeBound_binary h height,
    FlatAffineHeightSlabExceptional.massBound_binary h height⟩

noncomputable def roots (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → Finset ℝ :=
  IntegerPolynomialRootQueriesBits.rootSet (source F hcone height)

theorem countEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun u => BinaryNatCode.encode (roots F hcone height u).card) :=
  IntegerPolynomialRootQueriesBits.countEvaluator (access h hcone height hh)

theorem cutEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (σ : SignType) :
    SpaceFunction (fun q => BinaryNatCode.encode
      (IntegerPolynomialRootQueriesBits.cutCount (source F hcone height) σ q)) :=
  IntegerPolynomialRootQueriesBits.cutEvaluator (access h hcone height hh) σ

theorem cellEvaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceFunction (fun q => BinaryNatCode.encode
      (IntegerPolynomialRootQueriesBits.cellCode (source F hcone height) q)) :=
  IntegerPolynomialRootQueriesBits.cellEvaluator (access h hcone height hh)

theorem cell_mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.cellLanguage (source F hcone height) ∈ PSPACE :=
  IntegerPolynomialRootQueriesBits.cell_mem_PSPACE (access h hcone height hh)

theorem rational_gap_iff (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (k : Fin ((roots F hcone height (pairFst q)).card + 1)) :
    pair q (BinaryNatCode.encode ((roots F hcone height (pairFst q)).card + k.val)) ∈
        IntegerPolynomialRootQueriesBits.cellLanguage (source F hcone height) ↔
      RationalCutBits.threshold q ∈ gap (roots F hcone height (pairFst q)) k :=
  IntegerPolynomialRootQueriesBits.cell_packet (source F hcone height) q (.inr k)

theorem mem_roots_iff (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (t : ℝ) :
    t ∈ roots F hcone height u ↔
      SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineHeightSlabExceptional.polynomial F height u) = 0 := by
  have hn : (FlatAffineHeightSlabExceptional.polynomial F height u).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr
      (FlatAffineHeightSlabExceptional.ne_zero F hcone height u)
  simp only [roots, IntegerPolynomialRootQueriesBits.rootSet, source, algebraMap_int_eq,
    Multiset.mem_toFinset, Polynomial.mem_roots hn, Polynomial.IsRoot, Polynomial.eval_map,
    SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom]

theorem gap_avoids (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (k : Fin ((roots F hcone height u).card + 1)) (t : ℝ) (ht : t ∈ gap (roots F hcone height u) k) :
    SymbolicScaledSquarefree.scalarEvaluation t (Connectivity.FlatAffineHeightArcs.exceptional F height u) ≠ 0 := by
  apply FlatAffineHeightSlabExceptional.avoids _ F hcone height u
  exact (mem_roots_iff F hcone height u t).not.mp (gap_no_root _ k ht)

end LeanCanny.Encoding.FlatAffineHeightCells
