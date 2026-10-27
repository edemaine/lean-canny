/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FormulaRationalSource

/-! # Native connectivity in guarded rational-coordinate slices

The constructed atom and denominator factors give sign-invariant real cells.
The guard circuit selects exactly those points where all allowed coordinate
denominators are nonzero and the original formula holds in their ratios.
Connectivity is decided in this actual set, including holes at poles.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaRationalSlice
open Set Polynomial LeanCanny.ETR LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedAlgebraicSlice FormulaRationalSource AlgebraicSliceBooleanAtoms
open scoped Classical

attribute [local irreducible] FormulaBooleanCircuitSource.circuit FormulaBooleanCircuitSource.termOfReader

noncomputable def domain (read : List Bool → List Bool) (D : BivariateQueryProductBits.Family)
    (c : List Bool) (β x : ℝ) : Prop :=
  ∀ i, i < FormulaAtomPolynomials.budget read c → ((D.polynomial c i).map (ParameterTarski.evalHom β)).eval x ≠ 0

theorem denominator_eval (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (i : ℕ) (x : ℝ) :
    (BoundedAlgebraicSliceIndexed.value P (family read N D) u
      ((FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u) + i)).eval x =
        ((D.polynomial (pairFst u) i).map (ParameterTarski.evalHom (point P u))).eval x := by
  rw [BoundedAlgebraicSliceIndexed.value_valid P (family read N D) u _ hu]
  have hc : (FormulaRationalAtoms.family read N D).count (pairFst u) =
      (FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u) := rfl
  simp only [family, BivariateQueryProductBits.Family.append, hc]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rfl

theorem atom_sign (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) (hd : domain read D (pairFst u) (point P u) x)
    (i : ℕ) (hi : i < (FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u)) :
    SignType.sign ((BoundedAlgebraicSliceIndexed.value P (family read N D) u i).eval x) =
      SignType.sign ((FormulaBooleanCircuitSource.termOfReader read (pair (pairFst u) (BinaryNatCode.encode i))).eval
        (BivariateRationalTermReader.environment N D (pairFst u) (point P u) x)) := by
  rw [BoundedAlgebraicSliceIndexed.value_valid P (family read N D) u i hu]
  have hi' : i < (FormulaRationalAtoms.family read N D).count (pairFst u) := hi
  simp only [family, BivariateQueryProductBits.Family.append, hi', ite_true]
  have hden : ∀ j, j < Nat.fromBitsLE ((FormulaAtomPolynomials.termSource read).arity
      (pair (pairFst u) (BinaryNatCode.encode i))) →
      (((D.comp pairFst).polynomial (pair (pairFst u) (BinaryNatCode.encode i)) j).map
        (ParameterTarski.evalHom (point P u))).eval x ≠ 0 := by
    intro j hj
    rw [FormulaRationalAtoms.source_arity] at hj
    simpa only [BivariateQueryProductBits.Family.comp, pairFst_pair] using
      hd j (hj.trans_le (FormulaAtomPolynomials.term_size_le read (pairFst u) i))
  have H := BivariateRationalTermReader.sign_specialize (FormulaAtomPolynomials.termSource read)
    (N.comp pairFst) (D.comp pairFst) (pair (pairFst u) (BinaryNatCode.encode i)) (point P u) x hden
  have he : BivariateRationalTermReader.environment (N.comp pairFst) (D.comp pairFst)
      (pair (pairFst u) (BinaryNatCode.encode i)) (point P u) x =
      BivariateRationalTermReader.environment N D (pairFst u) (point P u) x := by
    funext j
    simp only [BivariateRationalTermReader.environment, BivariateQueryProductBits.Family.comp, pairFst_pair]
  rw [he, FormulaRationalAtoms.source_syntax] at H
  simpa only [FormulaRationalAtoms.family, FormulaRationalAtoms.atomPolynomial] using H

attribute [local irreducible] family source

theorem guard_iff (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) (i : ℕ) (hi : i < FormulaAtomPolynomials.budget read (pairFst u)) :
    semanticAtom (source read) (AlgebraicSliceCellCover.signVector P (family read N D) u x)
      (pair (pairFst u) (BinaryNatCode.encode ((FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u) + 3 * i))) = false ↔
      ((D.polynomial (pairFst u) i).map (ParameterTarski.evalHom (point P u))).eval x ≠ 0 := by
  have hg := guard_factor read (pairFst u) i
  have hcount : (FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u) + i < (family read N D).count (pairFst u) := by
    rw [family_count]
    omega
  simp only [semanticAtom, hg.1, hg.2]
  rw [dite_eq_left hcount]
  change decide (SignType.sign ((BoundedAlgebraicSliceIndexed.value P (family read N D) u
    ((FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u) + i)).eval x) = 0) = false ↔ _
  rw [denominator_eval P read N D u hu i x]
  simp only [decide_eq_false_iff_not, sign_eq_zero_iff]

theorem truth_iff (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) :
    AlgebraicSliceBooleanCells.truth (source read) (pairFst u)
      (AlgebraicSliceCellCover.signVector P (family read N D) u x) ↔
        domain read D (pairFst u) (point P u) x ∧
          (FormulaView.formula (read (pairFst u))).Holds
            (BivariateRationalTermReader.environment N D (pairFst u) (point P u) x) := by
  unfold AlgebraicSliceBooleanCells.truth
  rw [show (source read).circuit = BooleanCircuitGuards.extend (FormulaBooleanCircuitSource.ofReader read).circuit
    (FormulaAtomPolynomials.budget read) by unfold source; rfl]
  rw [BooleanCircuitGuards.value_true _ _ _ _ (count_pos read (pairFst u)), original_value]
  have hguard : (∀ i, i < FormulaAtomPolynomials.budget read (pairFst u) →
      semanticAtom (source read) (AlgebraicSliceCellCover.signVector P (family read N D) u x)
        (pair (pairFst u) (BinaryNatCode.encode ((FormulaBooleanCircuitSource.ofReader read).circuit.count (pairFst u) + 3 * i))) = false) ↔
        domain read D (pairFst u) (point P u) x :=
    forall_congr' (fun i => forall_congr' (fun hi => guard_iff P read N D u hu x i hi))
  rw [hguard, and_comm]
  apply and_congr_right
  intro hd
  apply FormulaBooleanCircuitSource.signature_reader read _ _ _ (by
    rw [family_count]
    exact Nat.le_add_right _ _)
  intro i hi
  exact atom_sign P read N D u hu x hd i hi

noncomputable def solutionSet (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) : Set ℝ := {x |
  domain read D (pairFst u) (point P u) x ∧ (FormulaView.formula (read (pairFst u))).Holds
    (BivariateRationalTermReader.environment N D (pairFst u) (point P u) x)}

theorem solutionSet_eq (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) :
    AlgebraicSliceCellCover.solutionSet P (family read N D) u (AlgebraicSliceBooleanCells.truth (source read) (pairFst u)) =
      solutionSet P read N D u := by
  ext x
  exact truth_iff P read N D u hu x

noncomputable def connectedLanguage (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) : Language :=
  {u | u ∈ valid P ∧ IsPreconnected (solutionSet P read N D u)}

theorem connectedLanguage_eq (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) :
    connectedLanguage P read N D = AlgebraicSliceBooleanPSPACE.connectedLanguage P (family read N D) (source read) := by
  ext u
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hu
  have H := Topology.IsInducing.subtypeVal.isPreconnected_image
    (s := (univ : Set (AlgebraicSliceCellCover.solutionSet P (family read N D) u
      (AlgebraicSliceBooleanCells.truth (source read) (pairFst u)))))
  simpa only [image_univ, Subtype.range_val, solutionSet_eq P read N D u hu] using H

theorem connected_mem_PSPACE {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {N D : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : connectedLanguage P read N D ∈ PSPACE := by
  rw [connectedLanguage_eq]
  exact AlgebraicSliceBooleanPSPACE.connected_mem_PSPACE h (family_access read hr A B) ha (source read) (source_access read hr)

theorem reachable_mem_PSPACE {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {N D : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    AlgebraicSliceBooleanReachability.language P (family read N D) (source read) ∈ PSPACE :=
  AlgebraicSliceBooleanReachability.mem_PSPACE h (family_access read hr A B) ha (source read) (source_access read hr)

theorem reachable_packet (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (c d : AlgebraicSliceCellCover.Index P (family read N D) u)
    (x y : ℝ) (hx : x ∈ solutionSet P read N D u) (hy : y ∈ solutionSet P read N D u)
    (hxc : x ∈ AlgebraicSliceCellCover.piece P (family read N D) u c)
    (hyd : y ∈ AlgebraicSliceCellCover.piece P (family read N D) u d) :
    pair u (pair (AlgebraicSliceCellLabels.label P (family read N D) u c)
      (AlgebraicSliceCellLabels.label P (family read N D) u d)) ∈
        AlgebraicSliceBooleanReachability.language P (family read N D) (source read) ↔
          JoinedIn (solutionSet P read N D u) x y := by
  let x' : AlgebraicSliceCellCover.solutionSet P (family read N D) u
      (AlgebraicSliceBooleanCells.truth (source read) (pairFst u)) :=
    ⟨x, by rw [solutionSet_eq P read N D u hu]; exact hx⟩
  let y' : AlgebraicSliceCellCover.solutionSet P (family read N D) u
      (AlgebraicSliceBooleanCells.truth (source read) (pairFst u)) :=
    ⟨y, by rw [solutionSet_eq P read N D u hu]; exact hy⟩
  have H := AlgebraicSliceBooleanReachability.packet P (family read N D) (source read)
    u hu c d (x := x') (y := y') hxc hyd
  rw [joinedIn_univ] at H
  refine H.trans ?_
  rw [← solutionSet_eq P read N D u hu]
  exact (joinedIn_iff_joined x'.property y'.property).symm

end LeanCanny.Connectivity.FormulaRationalSlice
