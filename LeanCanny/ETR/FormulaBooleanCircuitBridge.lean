/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaBooleanCircuitCorrect
public import LeanCanny.Connectivity.AlgebraicSliceBooleanReachability

/-! # Original formula truth from indexed factor signatures

The source circuit uses its own gate index as the factor index. A signature
agreeing with the signs of the preserved arithmetic terms therefore evaluates
the original formula, including nested negations and strict inequalities.
-/

@[expose] public section
namespace LeanCanny.ETR.FormulaBooleanCircuitSource
open LeanCanny.Computation LeanCanny.Encoding
open Connectivity.AlgebraicSliceBooleanAtoms
open scoped Classical

theorem value_signature {n : ℕ} (Γ : Fin n → SignType) (σ : Term → SignType) (c : List Bool)
    (hn : circuit.count c ≤ n)
    (hΓ : ∀ i (hi : i < circuit.count c), Γ ⟨i, hi.trans_le hn⟩ = σ (term (pair c (BinaryNatCode.encode i)))) :
    BooleanCircuitSpace.value source.circuit (semanticAtom source Γ) c = evalSign σ (FormulaView.formula c) := by
  have ha : ∀ i < circuit.count c,
      semanticAtom source Γ (pair c (BinaryNatCode.encode i)) = atom σ (pair c (BinaryNatCode.encode i)) := by
    intro i hi
    have hin : i < n := hi.trans_le hn
    simp only [semanticAtom, source, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [dite_eq_left hin, hΓ i hi]
    rfl
  change BooleanCircuitSpace.value circuit (semanticAtom source Γ) c = _
  unfold BooleanCircuitSpace.value
  rw [BooleanCircuitSpace.values_congr circuit (semanticAtom source Γ) (atom σ) c _ ha]
  exact value_formula σ c

theorem signature_holds {n : ℕ} (Γ : Fin n → SignType) (env : ℕ → ℝ) (c : List Bool)
    (hn : circuit.count c ≤ n)
    (hΓ : ∀ i (hi : i < circuit.count c), Γ ⟨i, hi.trans_le hn⟩ = SignType.sign ((term (pair c (BinaryNatCode.encode i))).eval env)) :
    Connectivity.AlgebraicSliceBooleanCells.truth source c Γ ↔ (FormulaView.formula c).Holds env := by
  unfold Connectivity.AlgebraicSliceBooleanCells.truth
  rw [value_signature Γ (fun t => SignType.sign (t.eval env)) c hn hΓ, evalSign_holds]

theorem signature_encode {n : ℕ} (Γ : Fin n → SignType) (env : ℕ → ℝ) (p : Formula)
    (hn : circuit.count p.encode ≤ n)
    (hΓ : ∀ i (hi : i < circuit.count p.encode), Γ ⟨i, hi.trans_le hn⟩ = SignType.sign ((term (pair p.encode (BinaryNatCode.encode i))).eval env)) :
    Connectivity.AlgebraicSliceBooleanCells.truth source p.encode Γ ↔ p.Holds env := by
  simpa only [FormulaView.formula_encode] using signature_holds Γ env p.encode hn hΓ

theorem signature_reader {n : ℕ} (read : List Bool → List Bool) (Γ : Fin n → SignType) (env : ℕ → ℝ) (c : List Bool)
    (hn : circuit.count (read c) ≤ n)
    (hΓ : ∀ i (hi : i < circuit.count (read c)), Γ ⟨i, hi.trans_le hn⟩ =
      SignType.sign ((termOfReader read (pair c (BinaryNatCode.encode i))).eval env)) :
    Connectivity.AlgebraicSliceBooleanCells.truth (ofReader read) c Γ ↔ (FormulaView.formula (read c)).Holds env := by
  have he : ∀ k < circuit.count (read c), semanticAtom (ofReader read) Γ (pair c (BinaryNatCode.encode k)) =
      semanticAtom source Γ (pair (read c) (BinaryNatCode.encode k)) := by
    intro k _
    simp only [semanticAtom, ofReader, source, readerQuery, pairFst_pair, pairSnd_pair]
  change BooleanCircuitSpace.value (circuit.comp read) (semanticAtom (ofReader read) Γ) c = true ↔ _
  rw [BooleanCircuitSpace.value_comp circuit read _ (semanticAtom source Γ) c he]
  apply signature_holds Γ env (read c) hn
  intro i hi
  simpa only [termOfReader, readerQuery, pairFst_pair, pairSnd_pair] using hΓ i hi

theorem connected_mem_PSPACE {P : BoundedFullWriter.Readers} (h : P.PolyTime) {Q : LeanCanny.Algebra.BivariateQueryProductBits.Family}
    (A : LeanCanny.Algebra.BivariateQueryProductBits.Access Q)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    Connectivity.AlgebraicSliceBooleanPSPACE.connectedLanguage P Q source ∈ PSPACE :=
  Connectivity.AlgebraicSliceBooleanPSPACE.connected_mem_PSPACE h A ha source access

theorem reachable_mem_PSPACE {P : BoundedFullWriter.Readers} (h : P.PolyTime) {Q : LeanCanny.Algebra.BivariateQueryProductBits.Family}
    (A : LeanCanny.Algebra.BivariateQueryProductBits.Access Q)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    Connectivity.AlgebraicSliceBooleanReachability.language P Q source ∈ PSPACE :=
  Connectivity.AlgebraicSliceBooleanReachability.mem_PSPACE h A ha source access

theorem connected_reader_mem_PSPACE {P : BoundedFullWriter.Readers} (h : P.PolyTime) {Q : LeanCanny.Algebra.BivariateQueryProductBits.Family}
    (A : LeanCanny.Algebra.BivariateQueryProductBits.Access Q)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (read : List Bool → List Bool) (hr : read ∈ FP) :
    Connectivity.AlgebraicSliceBooleanPSPACE.connectedLanguage P Q (ofReader read) ∈ PSPACE :=
  Connectivity.AlgebraicSliceBooleanPSPACE.connected_mem_PSPACE h A ha (ofReader read) (accessOfReader read hr)

theorem reachable_reader_mem_PSPACE {P : BoundedFullWriter.Readers} (h : P.PolyTime) {Q : LeanCanny.Algebra.BivariateQueryProductBits.Family}
    (A : LeanCanny.Algebra.BivariateQueryProductBits.Access Q)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (read : List Bool → List Bool) (hr : read ∈ FP) :
    Connectivity.AlgebraicSliceBooleanReachability.language P Q (ofReader read) ∈ PSPACE :=
  Connectivity.AlgebraicSliceBooleanReachability.mem_PSPACE h A ha (ofReader read) (accessOfReader read hr)

end LeanCanny.ETR.FormulaBooleanCircuitSource
