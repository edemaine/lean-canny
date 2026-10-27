/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FormulaRationalAtoms
public import LeanCanny.Algebra.BivariateQueryAppend
public import LeanCanny.Computation.BooleanCircuitGuards
public import LeanCanny.ETR.FormulaBooleanCircuitBridge

/-! # Constructed formula circuits with denominator guards

The factor family appends all coordinate denominators in the formula's size
allowance. Their roots participate in the cell decomposition, and a native
guard chain excludes every pole before accepting a formula-selected cell.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FormulaRationalSource
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open FormulaAtomPolynomials FormulaBooleanCircuitSource AlgebraicSliceBooleanAtoms
open scoped Classical

attribute [local irreducible] FormulaBooleanCircuitSource.circuit FormulaBooleanCircuitSource.requested

theorem budget_unary (read : List Bool → List Bool) (hr : read ∈ FP) : UnaryFn (budget read) :=
  (UnaryFn.length (mem_FP_comp hr FormulaView.normalize_mem_FP)).add (UnaryFn.const 10)

def denominators (read : List Bool → List Bool) (D : BivariateQueryProductBits.Family) : BivariateQueryProductBits.Family :=
  { D with count := budget read }

def denominators_access (read : List Bool → List Bool) (hr : read ∈ FP) {D : BivariateQueryProductBits.Family}
    (B : BivariateQueryProductBits.Access D) : BivariateQueryProductBits.Access (denominators read D) :=
  { B with count_binary := budget_binary read hr }

noncomputable def family (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) : BivariateQueryProductBits.Family :=
  (FormulaRationalAtoms.family read N D).append (denominators read D)

theorem family_count (read : List Bool → List Bool) (N D : BivariateQueryProductBits.Family) (c : List Bool) :
    (family read N D).count c = (ofReader read).circuit.count c + budget read c := rfl

noncomputable def family_access (read : List Bool → List Bool) (hr : read ∈ FP) {N D : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access N) (B : BivariateQueryProductBits.Access D) : BivariateQueryProductBits.Access (family read N D) :=
  (FormulaRationalAtoms.access read hr A B).append (denominators_access read hr B)

def source (read : List Bool → List Bool) : Source where
  circuit := BooleanCircuitGuards.extend (ofReader read).circuit (budget read)
  factor q := if BooleanCircuitGuards.index q < (ofReader read).circuit.count (pairFst q)
    then Nat.fromBitsLE (pairSnd q)
    else (ofReader read).circuit.count (pairFst q) + BooleanCircuitGuards.delta (ofReader read).circuit q / 3
  sign q := if BooleanCircuitGuards.index q < (ofReader read).circuit.count (pairFst q) then (ofReader read).sign q else 0

theorem source_access (read : List Bool → List Bool) (hr : read ∈ FP) : Access (source read) := by
  have S := accessOfReader read hr
  have hi : BinaryFn BooleanCircuitGuards.index := BinaryFn.fromBits pairSnd_mem_FP
  have hn : BinaryFn (fun q => (ofReader read).circuit.count (pairFst q)) := (BinaryFn.ofUnary S.circuit.count).comp pairFst_mem_FP
  have hd : BinaryFn (BooleanCircuitGuards.delta (ofReader read).circuit) := hi.sub hn
  have hs := (hi.lt hn).ite_mem_FP S.sign (constFn_mem_FP (InfinitesimalSign.encode 0))
  refine ⟨BooleanCircuitGuards.access _ S.circuit _ (budget_unary read hr),
    BinaryFn.ite (hi.lt hn) hi (hn.add (hd.div (BinaryFn.const 3))),
    mem_FP_of_eq hs ?_⟩
  intro q
  simp only [source]
  split_ifs <;> rfl

theorem count_pos (read : List Bool → List Bool) (c : List Bool) : 0 < (ofReader read).circuit.count c := by
  simp only [ofReader, BooleanCircuitSpace.Family.comp, FormulaBooleanCircuitSource.circuit]
  rw [FormulaView.normalize_eq_formula]
  simp [Formula.encode]

theorem prefix_factor (read : List Bool → List Bool) (c : List Bool) (i : ℕ)
    (hi : i < (ofReader read).circuit.count c) :
    (source read).factor (pair c (BinaryNatCode.encode i)) = i ∧
      (source read).sign (pair c (BinaryNatCode.encode i)) = (ofReader read).sign (pair c (BinaryNatCode.encode i)) := by
  simp only [source, BooleanCircuitGuards.index, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, hi, ite_true]
  exact ⟨trivial, trivial⟩

theorem guard_factor (read : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    (source read).factor (pair c (BinaryNatCode.encode ((ofReader read).circuit.count c + 3 * i))) =
      (ofReader read).circuit.count c + i ∧
    (source read).sign (pair c (BinaryNatCode.encode ((ofReader read).circuit.count c + 3 * i))) = 0 := by
  simp only [source, BooleanCircuitGuards.index, BooleanCircuitGuards.delta, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs <;> simp_all

theorem original_value {n : ℕ} (read : List Bool → List Bool) (σ : Fin n → SignType) (c : List Bool) :
    BooleanCircuitSpace.value (ofReader read).circuit (semanticAtom (source read) σ) c =
      BooleanCircuitSpace.value (ofReader read).circuit (semanticAtom (ofReader read) σ) c := by
  unfold BooleanCircuitSpace.value
  rw [BooleanCircuitSpace.values_congr _ _ _ c _ (fun i hi => ?_)]
  have hp := prefix_factor read c i hi
  have ho : (ofReader read).factor (pair c (BinaryNatCode.encode i)) = i := by
    simp only [ofReader, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [semanticAtom, hp.1, hp.2, ho]

end LeanCanny.Connectivity.FormulaRationalSource
