/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FormulaRationalSource
public import LeanCanny.Connectivity.CriticalSampleSliceBooleanReachability

/-! # Native formula connectivity over actual critical samples

The base word retains an actual sample descriptor and an independent query record.
The constructed atom and denominator factors give sign-invariant real cells.
The guard circuit selects exactly those points where all allowed coordinate
denominators are nonzero and the original formula holds in their ratios.
Connectivity is decided in this actual set, including holes at poles.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaCriticalSampleRationalSlice
open Set Polynomial LeanCanny.ETR LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedCriticalSampleSlice FormulaRationalSource CriticalSampleSliceBooleanAtoms
open scoped Classical

attribute [local irreducible] FormulaBooleanCircuitSource.circuit FormulaBooleanCircuitSource.termOfReader

noncomputable def domain (read : List Bool → List Bool) (D : BivariateQueryProductBits.Family)
    (c : List Bool) (β x : ℝ) : Prop :=
  ∀ i, i < FormulaAtomPolynomials.budget read c → ((D.polynomial c i).map (ParameterTarski.evalHom β)).eval x ≠ 0

theorem denominator_eval (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (i : ℕ) (x : ℝ) :
    (BoundedCriticalSampleSliceIndexed.value P (family read N D) u
      ((FormulaBooleanCircuitSource.ofReader read).circuit.count (context u) + i)).eval x =
        ((D.polynomial (context u) i).map (ParameterTarski.evalHom (point P (pairFst u)))).eval x := by
  rw [BoundedCriticalSampleSliceIndexed.value_valid P (family read N D) u _ hu]
  have hc : (FormulaRationalAtoms.family read N D).count (context u) =
      (FormulaBooleanCircuitSource.ofReader read).circuit.count (context u) := rfl
  simp only [family, BivariateQueryProductBits.Family.append, hc]
  rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
  rfl

theorem atom_sign (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) (hd : domain read D (context u) (point P (pairFst u)) x)
    (i : ℕ) (hi : i < (FormulaBooleanCircuitSource.ofReader read).circuit.count (context u)) :
    SignType.sign ((BoundedCriticalSampleSliceIndexed.value P (family read N D) u i).eval x) =
      SignType.sign ((FormulaBooleanCircuitSource.termOfReader read (pair (context u) (BinaryNatCode.encode i))).eval
        (BivariateRationalTermReader.environment N D (context u) (point P (pairFst u)) x)) := by
  rw [BoundedCriticalSampleSliceIndexed.value_valid P (family read N D) u i hu]
  have hi' : i < (FormulaRationalAtoms.family read N D).count (context u) := hi
  simp only [family, BivariateQueryProductBits.Family.append, hi', ite_true]
  have hden : ∀ j, j < Nat.fromBitsLE ((FormulaAtomPolynomials.termSource read).arity
      (pair (context u) (BinaryNatCode.encode i))) →
      (((D.comp pairFst).polynomial (pair (context u) (BinaryNatCode.encode i)) j).map
        (ParameterTarski.evalHom (point P (pairFst u)))).eval x ≠ 0 := by
    intro j hj
    rw [FormulaRationalAtoms.source_arity] at hj
    simpa only [BivariateQueryProductBits.Family.comp, pairFst_pair] using
      hd j (hj.trans_le (FormulaAtomPolynomials.term_size_le read (context u) i))
  have H := BivariateRationalTermReader.sign_specialize (FormulaAtomPolynomials.termSource read)
    (N.comp pairFst) (D.comp pairFst) (pair (context u) (BinaryNatCode.encode i)) (point P (pairFst u)) x hden
  have he : BivariateRationalTermReader.environment (N.comp pairFst) (D.comp pairFst)
      (pair (context u) (BinaryNatCode.encode i)) (point P (pairFst u)) x =
      BivariateRationalTermReader.environment N D (context u) (point P (pairFst u)) x := by
    funext j
    simp only [BivariateRationalTermReader.environment, BivariateQueryProductBits.Family.comp, pairFst_pair]
  rw [he, FormulaRationalAtoms.source_syntax] at H
  simpa only [FormulaRationalAtoms.family, FormulaRationalAtoms.atomPolynomial] using H

attribute [local irreducible] family source

theorem guard_iff (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) (i : ℕ) (hi : i < FormulaAtomPolynomials.budget read (context u)) :
    semanticAtom (source read) (CriticalSampleSliceCellCover.signVector P (family read N D) u x)
      (pair (context u) (BinaryNatCode.encode ((FormulaBooleanCircuitSource.ofReader read).circuit.count (context u) + 3 * i))) = false ↔
      ((D.polynomial (context u) i).map (ParameterTarski.evalHom (point P (pairFst u)))).eval x ≠ 0 := by
  have hg := guard_factor read (context u) i
  have hcount : (FormulaBooleanCircuitSource.ofReader read).circuit.count (context u) + i < (family read N D).count (context u) := by
    rw [family_count]
    omega
  simp only [semanticAtom, hg.1, hg.2]
  rw [dite_eq_left hcount]
  change decide (SignType.sign ((BoundedCriticalSampleSliceIndexed.value P (family read N D) u
    ((FormulaBooleanCircuitSource.ofReader read).circuit.count (context u) + i)).eval x) = 0) = false ↔ _
  rw [denominator_eval P read N D u hu i x]
  simp only [decide_eq_false_iff_not, sign_eq_zero_iff]

theorem truth_iff (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (x : ℝ) :
    CriticalSampleSliceBooleanCells.truth (source read) (context u)
      (CriticalSampleSliceCellCover.signVector P (family read N D) u x) ↔
        domain read D (context u) (point P (pairFst u)) x ∧
          (FormulaView.formula (read (context u))).Holds
            (BivariateRationalTermReader.environment N D (context u) (point P (pairFst u)) x) := by
  unfold CriticalSampleSliceBooleanCells.truth
  rw [show (source read).circuit = BooleanCircuitGuards.extend (FormulaBooleanCircuitSource.ofReader read).circuit
    (FormulaAtomPolynomials.budget read) by unfold source; rfl]
  rw [BooleanCircuitGuards.value_true _ _ _ _ (count_pos read (context u)), original_value]
  have hguard : (∀ i, i < FormulaAtomPolynomials.budget read (context u) →
      semanticAtom (source read) (CriticalSampleSliceCellCover.signVector P (family read N D) u x)
        (pair (context u) (BinaryNatCode.encode ((FormulaBooleanCircuitSource.ofReader read).circuit.count (context u) + 3 * i))) = false) ↔
        domain read D (context u) (point P (pairFst u)) x :=
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
  domain read D (context u) (point P (pairFst u)) x ∧ (FormulaView.formula (read (context u))).Holds
    (BivariateRationalTermReader.environment N D (context u) (point P (pairFst u)) x)}

theorem solutionSet_eq (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) :
    CriticalSampleSliceCellCover.solutionSet P (family read N D) u (CriticalSampleSliceBooleanCells.truth (source read) (context u)) =
      solutionSet P read N D u := by
  ext x
  exact truth_iff P read N D u hu x

noncomputable def connectedLanguage (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) : Language :=
  {u | u ∈ valid P ∧ IsPreconnected (solutionSet P read N D u)}

theorem connectedLanguage_eq (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) :
    connectedLanguage P read N D = CriticalSampleSliceBooleanPSPACE.connectedLanguage P (family read N D) (source read) := by
  ext u
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hu
  have H := Topology.IsInducing.subtypeVal.isPreconnected_image
    (s := (univ : Set (CriticalSampleSliceCellCover.solutionSet P (family read N D) u
      (CriticalSampleSliceBooleanCells.truth (source read) (context u)))))
  simpa only [image_univ, Subtype.range_val, solutionSet_eq P read N D u hu] using H

theorem connected_mem_PSPACE {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {N D : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : connectedLanguage P read N D ∈ PSPACE := by
  rw [connectedLanguage_eq]
  exact CriticalSampleSliceBooleanPSPACE.connected_mem_PSPACE h (family_access read hr A B) ha (source read) (source_access read hr)

theorem reachable_mem_PSPACE {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    {N D : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    CriticalSampleSliceBooleanReachability.language P (family read N D) (source read) ∈ PSPACE :=
  CriticalSampleSliceBooleanReachability.mem_PSPACE h (family_access read hr A B) ha (source read) (source_access read hr)

theorem reachable_packet (P : Readers) (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family)
    (u : List Bool) (hu : u ∈ valid P) (c d : CriticalSampleSliceCellCover.Index P (family read N D) u)
    (x y : ℝ) (hx : x ∈ solutionSet P read N D u) (hy : y ∈ solutionSet P read N D u)
    (hxc : x ∈ CriticalSampleSliceCellCover.piece P (family read N D) u c)
    (hyd : y ∈ CriticalSampleSliceCellCover.piece P (family read N D) u d) :
    pair u (pair (CriticalSampleSliceCellLabels.label P (family read N D) u c)
      (CriticalSampleSliceCellLabels.label P (family read N D) u d)) ∈
        CriticalSampleSliceBooleanReachability.language P (family read N D) (source read) ↔
          JoinedIn (solutionSet P read N D u) x y := by
  let x' : CriticalSampleSliceCellCover.solutionSet P (family read N D) u
      (CriticalSampleSliceBooleanCells.truth (source read) (context u)) :=
    ⟨x, by rw [solutionSet_eq P read N D u hu]; exact hx⟩
  let y' : CriticalSampleSliceCellCover.solutionSet P (family read N D) u
      (CriticalSampleSliceBooleanCells.truth (source read) (context u)) :=
    ⟨y, by rw [solutionSet_eq P read N D u hu]; exact hy⟩
  have H := CriticalSampleSliceBooleanReachability.packet P (family read N D) (source read)
    u hu c d (x := x') (y := y') hxc hyd
  rw [joinedIn_univ] at H
  refine H.trans ?_
  rw [← solutionSet_eq P read N D u hu]
  exact (joinedIn_iff_joined x'.property y'.property).symm

end LeanCanny.Connectivity.FormulaCriticalSampleRationalSlice
