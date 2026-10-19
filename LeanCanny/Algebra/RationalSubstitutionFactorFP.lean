/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionFactors
public import LeanCanny.Algebra.PolynomialProductSpace
public import LeanCanny.Encoding.BinaryDivFP

/-!
# Encoded access to cleared-monomial factors

The packet `pair context (pair flatIndex degree)` selects one coefficient.
Binary quotient/remainder identify the variable and its position in the block.
An FP exponent writer selects the numerator or denominator coefficient child.
Only valid variable addresses need a source correctness contract.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.FactorBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

def index (p : List Bool) : List Bool := pairFst (pairSnd p)
def degree (p : List Bool) : List Bool := pairSnd (pairSnd p)
def coordinate (width : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.divMod (pair (index p) (width (pairFst p)))
def varIndex (width : List Bool → List Bool) (p : List Bool) : List Bool := pairFst (coordinate width p)
def position (width : List Bool → List Bool) (p : List Bool) : List Bool := pairSnd (coordinate width p)
def exponentQuery (width : List Bool → List Bool) (p : List Bool) : List Bool := pair (pairFst p) (varIndex width p)
def coefficientQuery (width : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (varIndex width p) (degree p))
def numeratorSelected (width exponent : List Bool → List Bool) (p : List Bool) : Bool :=
  decide (Nat.fromBitsLE (position width p) < Nat.fromBitsLE (exponent (exponentQuery width p)))
def value (width exponent n d : List Bool → List Bool) (p : List Bool) : List Bool :=
  if numeratorSelected width exponent p then n (coefficientQuery width p) else d (coefficientQuery width p)

theorem index_mem_FP : index ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem degree_mem_FP : degree ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem coordinate_mem_FP {width : List Bool → List Bool} (hw : width ∈ FP) : coordinate width ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair index_mem_FP (mem_FP_comp pairFst_mem_FP hw)) BinaryNat.divMod_mem_FP
  refine mem_FP_of_eq (g := coordinate width) h ?_
  intro p
  simp only [Function.comp_apply, coordinate]
theorem varIndex_mem_FP {width : List Bool → List Bool} (hw : width ∈ FP) : varIndex width ∈ FP :=
  mem_FP_comp (coordinate_mem_FP hw) pairFst_mem_FP
theorem position_mem_FP {width : List Bool → List Bool} (hw : width ∈ FP) : position width ∈ FP :=
  mem_FP_comp (coordinate_mem_FP hw) pairSnd_mem_FP
theorem exponentQuery_mem_FP {width : List Bool → List Bool} (hw : width ∈ FP) : exponentQuery width ∈ FP :=
  mem_FP_pair pairFst_mem_FP (varIndex_mem_FP hw)
theorem coefficientQuery_mem_FP {width : List Bool → List Bool} (hw : width ∈ FP) : coefficientQuery width ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair (varIndex_mem_FP hw) degree_mem_FP)
theorem numeratorSelected_mem_FP {width exponent : List Bool → List Bool} (hw : width ∈ FP) (he : exponent ∈ FP) :
    (fun p => [numeratorSelected width exponent p]) ∈ FP := by
  have hx := mem_FP_comp (exponentQuery_mem_FP hw) he
  exact (BinaryNat.lt_fppred (position_mem_FP hw) hx).flag_mem_FP

noncomputable def evaluator {n d : List Bool → List Bool} (N : SpaceFunction n) (D : SpaceFunction d)
    (width exponent : List Bool → List Bool) (hw : width ∈ FP) (he : exponent ∈ FP) :
    SpaceFunction (value width exponent n d) := by
  let Q := SpaceFunction.branch (numeratorSelected width exponent) (numeratorSelected_mem_FP hw he)
    (N.precompose (coefficientQuery width) (coefficientQuery_mem_FP hw))
    (D.precompose (coefficientQuery width) (coefficientQuery_mem_FP hw))
  refine Q.congr (funext fun p => ?_)
  simp only [value, Function.comp_apply]

theorem coordinate_packet (width : List Bool → List Bool) (c : List Bool) (j k : ℕ) :
    coordinate width (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) =
      pair (BinaryNatCode.encode (j / Nat.fromBitsLE (width c)))
        (BinaryNatCode.encode (j % Nat.fromBitsLE (width c))) := by
  simp only [coordinate, index, pairFst_pair, pairSnd_pair, BinaryNat.divMod_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem exponentQuery_packet (width : List Bool → List Bool) (c : List Bool) (j k : ℕ) :
    exponentQuery width (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) =
      pair c (BinaryNatCode.encode (j / Nat.fromBitsLE (width c))) := by
  simp only [exponentQuery, varIndex, coordinate_packet, pairFst_pair]

theorem coefficientQuery_packet (width : List Bool → List Bool) (c : List Bool) (j k : ℕ) :
    coefficientQuery width (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) =
      pair c (pair (BinaryNatCode.encode (j / Nat.fromBitsLE (width c))) (BinaryNatCode.encode k)) := by
  simp only [coefficientQuery, varIndex, degree, coordinate_packet, pairFst_pair, pairSnd_pair]

theorem value_packet (width exponent n d : List Bool → List Bool) (c : List Bool)
    (m A : ℕ) (e : ℕ → ℕ) (np dp : ℕ → Polynomial (ZMod m))
    (he : ∀ i, i < A → Nat.fromBitsLE (exponent (pair c (BinaryNatCode.encode i))) = e i)
    (hn : ∀ i, i < A → ∀ k, n (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((np i).coeff k))
    (hd : ∀ i, i < A → ∀ k, d (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((dp i).coeff k))
    (j k : ℕ) (hj : j < A * Nat.fromBitsLE (width c)) :
    value width exponent n d (pair c (pair (BinaryNatCode.encode j) (BinaryNatCode.encode k))) =
      residueBits ((flatFactor np dp e (Nat.fromBitsLE (width c)) j).coeff k) := by
  have hW : 0 < Nat.fromBitsLE (width c) := by
    by_contra h
    have hz : Nat.fromBitsLE (width c) = 0 := by omega
    simp only [hz, Nat.mul_zero] at hj
    omega
  have hi : j / Nat.fromBitsLE (width c) < A := (Nat.div_lt_iff_lt_mul hW).mpr hj
  simp only [value, numeratorSelected, position, coordinate_packet, exponentQuery_packet,
    coefficientQuery_packet, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (j % Nat.fromBitsLE (width c))) =
      j % Nat.fromBitsLE (width c) from Nat.fromBitsLE_bits _, he _ hi]
  unfold flatFactor
  by_cases h : j % Nat.fromBitsLE (width c) < e (j / Nat.fromBitsLE (width c))
  · simp only [h, decide_true, ↓reduceIte]
    exact hn _ hi k
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact hd _ hi k

end LeanCanny.Algebra.RationalSubstitution.FactorBits
