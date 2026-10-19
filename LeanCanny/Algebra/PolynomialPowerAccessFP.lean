/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzQueryFP
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# Encoded access to coefficient matrices

An entry of a flattened coefficient matrix decodes two indices into an
original matrix coordinate and a degree coordinate. A lower triangular guard
selects one original coefficient query or zero. All preparation is FP, and
the selected coefficient routine may use polynomial space.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialPower
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open Berkowitz

structure Access where
  dimension : List Bool → List Bool
  modulus : List Bool → List Bool
  exponent : List Bool → List Bool
  row : List Bool → List Bool
  col : List Bool → List Bool
  degree : List Bool → List Bool
  coefficient : List Bool → List Bool

structure Access.ControlsPolyTime (a : Access) : Prop where
  dimension : a.dimension ∈ FP
  modulus : a.modulus ∈ FP
  exponent : a.exponent ∈ FP
  row : a.row ∈ FP
  col : a.col ∈ FP
  degree : a.degree ∈ FP

namespace Access

def width (a : Access) (c : List Bool) : List Bool := BinaryNat.succ (a.degree c)
def liftedDimension (a : Access) (c : List Bool) : List Bool := BinaryNat.mul (pair (a.dimension c) (width a c))
def liftedRow (a : Access) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.mul (pair (a.row c) (width a c))) (a.degree c))
def liftedCol (a : Access) (c : List Bool) : List Bool := BinaryNat.mul (pair (a.col c) (width a c))

theorem width_mem_FP (a : Access) (ha : a.ControlsPolyTime) : width a ∈ FP :=
  mem_FP_comp ha.degree BinaryNat.succ_mem_FP

theorem liftedDimension_mem_FP (a : Access) (ha : a.ControlsPolyTime) : liftedDimension a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.dimension (width_mem_FP a ha)) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := liftedDimension a) h ?_
  intro c
  simp only [Function.comp_apply, liftedDimension]

theorem liftedRow_mem_FP (a : Access) (ha : a.ControlsPolyTime) : liftedRow a ∈ FP := by
  have hp := mem_FP_comp (mem_FP_pair ha.row (width_mem_FP a ha)) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hp ha.degree) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := liftedRow a) h ?_
  intro c
  simp only [Function.comp_apply, liftedRow]

theorem liftedCol_mem_FP (a : Access) (ha : a.ControlsPolyTime) : liftedCol a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.col (width_mem_FP a ha)) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := liftedCol a) h ?_
  intro c
  simp only [Function.comp_apply, liftedCol]

def coefficientInput (a : Access) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (QueryBits.sourceLayer a.degree p)
    (pair (QueryBits.targetLayer a.degree p)
      (BinaryNat.sub (pair (QueryBits.sourceDegree a.degree p) (QueryBits.targetDegree a.degree p)))))

def lower (a : Access) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (QueryBits.targetDegree a.degree p) ≤ Nat.fromBitsLE (QueryBits.sourceDegree a.degree p))

def liftedEntry (a : Access) (p : List Bool) : List Bool :=
  if lower a p then a.coefficient (coefficientInput a p) else []

theorem coefficientInput_mem_FP (a : Access) (ha : a.ControlsPolyTime) : coefficientInput a ∈ FP := by
  have hd := mem_FP_comp
    (mem_FP_pair (QueryBits.sourceDegree_mem_FP ha.degree) (QueryBits.targetDegree_mem_FP ha.degree))
    BinaryNat.sub_mem_FP
  have h := mem_FP_pair pairFst_mem_FP
    (mem_FP_pair (QueryBits.sourceLayer_mem_FP ha.degree)
      (mem_FP_pair (QueryBits.targetLayer_mem_FP ha.degree) hd))
  refine mem_FP_of_eq (g := coefficientInput a) h ?_
  intro p
  simp only [Function.comp_apply, coefficientInput]

theorem lower_mem_FP (a : Access) (ha : a.ControlsPolyTime) : (fun p => [lower a p]) ∈ FP :=
  (BinaryNat.le_fppred (QueryBits.targetDegree_mem_FP ha.degree)
    (QueryBits.sourceDegree_mem_FP ha.degree)).flag_mem_FP

noncomputable def entryEvaluator (a : Access) (ha : a.ControlsPolyTime) (E : SpaceFunction a.coefficient) :
    SpaceFunction (liftedEntry a) := by
  have R := SpaceFunction.branch (lower a) (lower_mem_FP a ha)
    (E.precompose (coefficientInput a) (coefficientInput_mem_FP a ha))
    (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine R.congr ?_
  funext p
  simp only [liftedEntry, Function.comp_apply]

theorem liftedDimension_code (a : Access) (c : List Bool) (n d : ℕ)
    (hn : a.dimension c = BinaryNatCode.encode n) (hd : a.degree c = BinaryNatCode.encode d) :
    liftedDimension a c = BinaryNatCode.encode (n * (d + 1)) := by
  simp only [liftedDimension, width, hn, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem liftedRow_code (a : Access) (c : List Bool) (i d : ℕ)
    (hi : a.row c = BinaryNatCode.encode i) (hd : a.degree c = BinaryNatCode.encode d) :
    liftedRow a c = BinaryNatCode.encode (i * (d + 1) + d) := by
  simp only [liftedRow, width, hi, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem liftedCol_code (a : Access) (c : List Bool) (j d : ℕ)
    (hj : a.col c = BinaryNatCode.encode j) (hd : a.degree c = BinaryNatCode.encode d) :
    liftedCol a c = BinaryNatCode.encode (j * (d + 1)) := by
  simp only [liftedCol, width, hj, hd, BinaryNat.succ_eq_bits, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem coefficientInput_code (a : Access) (c : List Bool) (d i j : ℕ)
    (hd : a.degree c = BinaryNatCode.encode d) :
    coefficientInput a (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      pair c (pair (BinaryNatCode.encode (i / (d + 1)))
        (pair (BinaryNatCode.encode (j / (d + 1))) (BinaryNatCode.encode (i % (d + 1) - j % (d + 1))))) := by
  simp only [coefficientInput, QueryBits.sourceLayer_eq_code, QueryBits.targetLayer_eq_code,
    QueryBits.sourceDegree_eq_code, QueryBits.targetDegree_eq_code,
    QueryBits.rowIndex, QueryBits.colIndex, QueryBits.inputDimension, pairFst_pair, pairSnd_pair,
    hd, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem lower_code (a : Access) (c : List Bool) (d i j : ℕ)
    (hd : a.degree c = BinaryNatCode.encode d) :
    lower a (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      decide (j % (d + 1) ≤ i % (d + 1)) := by
  simp only [lower, QueryBits.sourceDegree_eq_code, QueryBits.targetDegree_eq_code,
    QueryBits.rowIndex, QueryBits.colIndex, QueryBits.inputDimension, pairFst_pair, pairSnd_pair,
    hd, QueryBits.code_value]

end Access
end LeanCanny.Algebra.PolynomialPower
