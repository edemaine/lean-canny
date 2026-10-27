/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaAtomPolynomials
public import LeanCanny.ETR.FormulaBooleanCircuitBridge

/-! # Connectivity of original formulas in algebraic slices

Atom polynomials and the Boolean circuit are constructed from the same source.
Specialization therefore selects exactly the original formula's solution set
in the supplied bivariate coordinates. Whole-set connectivity and paths
between selected cell labels have native polynomial-space algorithms.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaAlgebraicSlice
open Set Polynomial LeanCanny.ETR LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open BoundedFullWriter BoundedAlgebraicSlice FormulaAtomPolynomials
open scoped Classical

attribute [local irreducible] FormulaBooleanCircuitSource.circuit FormulaBooleanCircuitSource.termOfReader

noncomputable def environment (F : BivariateQueryProductBits.Family) (c : List Bool) (β x : ℝ) : ℕ → ℝ :=
  fun i => ((F.polynomial c i).map (ParameterTarski.evalHom β)).eval x

theorem eval_specialize (t : Term) (F : BivariateQueryProductBits.Family) (c : List Bool) (β x : ℝ) :
    ((t.eval (F.polynomial c)).map (ParameterTarski.evalHom β)).eval x = t.eval (environment F c β x) := by
  exact t.eval_hom ((Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (ParameterTarski.evalHom β))) (F.polynomial c)

theorem factor_eval (P : Readers) (F : BivariateQueryProductBits.Family) (read : List Bool → List Bool)
    (u : List Bool) (hu : u ∈ valid P) (i : ℕ) (x : ℝ) :
    (BoundedAlgebraicSliceIndexed.value P (family read F) u i).eval x =
      (FormulaBooleanCircuitSource.termOfReader read (pair (pairFst u) (BinaryNatCode.encode i))).eval
        (environment F (pairFst u) (point P u) x) := by
  rw [BoundedAlgebraicSliceIndexed.value_valid P (family read F) u i hu]
  exact eval_specialize _ F _ _ x

theorem truth_iff (P : Readers) (F : BivariateQueryProductBits.Family) (read : List Bool → List Bool)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) :
    AlgebraicSliceBooleanCells.truth (FormulaBooleanCircuitSource.ofReader read) (pairFst u)
      (AlgebraicSliceCellCover.signVector P (family read F) u x) ↔
        (FormulaView.formula (read (pairFst u))).Holds (environment F (pairFst u) (point P u) x) := by
  apply FormulaBooleanCircuitSource.signature_reader read _ _ _ (le_refl _)
  intro i _
  change SignType.sign ((BoundedAlgebraicSliceIndexed.value P (family read F) u i).eval x) = _
  rw [factor_eval P F read u hu i x]

noncomputable def solutionSet (P : Readers) (F : BivariateQueryProductBits.Family) (read : List Bool → List Bool)
    (u : List Bool) : Set ℝ :=
  {x | (FormulaView.formula (read (pairFst u))).Holds (environment F (pairFst u) (point P u) x)}

theorem solutionSet_eq (P : Readers) (F : BivariateQueryProductBits.Family) (read : List Bool → List Bool)
    (u : List Bool) (hu : u ∈ valid P) :
    AlgebraicSliceCellCover.solutionSet P (family read F) u
      (AlgebraicSliceBooleanCells.truth (FormulaBooleanCircuitSource.ofReader read) (pairFst u)) =
        solutionSet P F read u := by
  ext x
  exact truth_iff P F read u hu x

noncomputable def connectedLanguage (P : Readers) (F : BivariateQueryProductBits.Family)
    (read : List Bool → List Bool) : Language :=
  {u | u ∈ valid P ∧ IsPreconnected (solutionSet P F read u)}

theorem connectedLanguage_eq (P : Readers) (F : BivariateQueryProductBits.Family) (read : List Bool → List Bool) :
    connectedLanguage P F read = AlgebraicSliceBooleanPSPACE.connectedLanguage P (family read F)
      (FormulaBooleanCircuitSource.ofReader read) := by
  ext u
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hu
  have H := Topology.IsInducing.subtypeVal.isPreconnected_image
    (s := (univ : Set (AlgebraicSliceCellCover.solutionSet P (family read F) u
      (AlgebraicSliceBooleanCells.truth (FormulaBooleanCircuitSource.ofReader read) (pairFst u)))))
  simpa only [image_univ, Subtype.range_val, solutionSet_eq P F read u hu] using H

theorem connected_mem_PSPACE {P : Readers} (h : P.PolyTime) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (read : List Bool → List Bool) (hr : read ∈ FP) : connectedLanguage P F read ∈ PSPACE := by
  rw [connectedLanguage_eq]
  exact FormulaBooleanCircuitSource.connected_reader_mem_PSPACE h (access read hr A) ha read hr

theorem reachable_mem_PSPACE {P : Readers} (h : P.PolyTime) {F : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access F) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (read : List Bool → List Bool) (hr : read ∈ FP) :
    AlgebraicSliceBooleanReachability.language P (family read F) (FormulaBooleanCircuitSource.ofReader read) ∈ PSPACE :=
  FormulaBooleanCircuitSource.reachable_reader_mem_PSPACE h (access read hr A) ha read hr

theorem reachable_packet (P : Readers) (F : BivariateQueryProductBits.Family) (read : List Bool → List Bool)
    (u : List Bool) (hu : u ∈ valid P) (c d : AlgebraicSliceCellCover.Index P (family read F) u)
    (x y : ℝ) (hx : x ∈ solutionSet P F read u) (hy : y ∈ solutionSet P F read u)
    (hxc : x ∈ AlgebraicSliceCellCover.piece P (family read F) u c)
    (hyd : y ∈ AlgebraicSliceCellCover.piece P (family read F) u d) :
    pair u (pair (AlgebraicSliceCellLabels.label P (family read F) u c)
      (AlgebraicSliceCellLabels.label P (family read F) u d)) ∈
        AlgebraicSliceBooleanReachability.language P (family read F) (FormulaBooleanCircuitSource.ofReader read) ↔
          JoinedIn (solutionSet P F read u) x y := by
  let x' : AlgebraicSliceCellCover.solutionSet P (family read F) u
      (AlgebraicSliceBooleanCells.truth (FormulaBooleanCircuitSource.ofReader read) (pairFst u)) :=
    ⟨x, by rw [solutionSet_eq P F read u hu]; exact hx⟩
  let y' : AlgebraicSliceCellCover.solutionSet P (family read F) u
      (AlgebraicSliceBooleanCells.truth (FormulaBooleanCircuitSource.ofReader read) (pairFst u)) :=
    ⟨y, by rw [solutionSet_eq P F read u hu]; exact hy⟩
  have H := AlgebraicSliceBooleanReachability.packet P (family read F) (FormulaBooleanCircuitSource.ofReader read)
    u hu c d (x := x') (y := y') hxc hyd
  rw [joinedIn_univ] at H
  refine H.trans ?_
  rw [← solutionSet_eq P F read u hu]
  exact (joinedIn_iff_joined x'.property y'.property).symm

end LeanCanny.Connectivity.FormulaAlgebraicSlice
