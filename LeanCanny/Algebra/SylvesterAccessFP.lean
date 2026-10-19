/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerDeterminantPSPACE

/-!
# Polynomial-time streamed access to Sylvester matrices

A modular entry request contains its modular context and two binary indices.
The two column blocks select a coefficient routine and a shifted coefficient
index. Guard tests and query writing use binary arithmetic; no coefficient list
or matrix is constructed. A separate writer computes the determinant bit budget.
-/

@[expose] public section

namespace LeanCanny.Algebra.SylvesterBits
open Complexity
open LeanCanny.Encoding

structure Access where
  leftDegree : List Bool → List Bool
  rightDegree : List Bool → List Bool
  coefficientBits : List Bool → List Bool
  leftCoefficient : List Bool → List Bool
  rightCoefficient : List Bool → List Bool

structure Access.PolyTime (a : Access) : Prop where
  leftDegree : a.leftDegree ∈ FP
  rightDegree : a.rightDegree ∈ FP
  coefficientBits : a.coefficientBits ∈ FP
  leftCoefficient : a.leftCoefficient ∈ FP
  rightCoefficient : a.rightCoefficient ∈ FP

def row (p : List Bool) : List Bool := pairFst (pairSnd p)
def col (p : List Bool) : List Bool := pairSnd (pairSnd p)
def context (p : List Bool) : List Bool := pairFst (pairFst p)
def leftDegree (a : Access) (p : List Bool) : List Bool := a.leftDegree (context p)
def rightDegree (a : Access) (p : List Bool) : List Bool := a.rightDegree (context p)

def rightShift (a : Access) (p : List Bool) : List Bool :=
  BinaryNat.sub (pair (col p) (leftDegree a p))

def coefficientInput (shift : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (BinaryNat.sub (pair (row p) (shift p)))

def bandEnd (width shift : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.add (pair (shift p) (width p))

def bandEntry (coefficient width shift : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (shift p) ≤ Nat.fromBitsLE (row p) ∧
      Nat.fromBitsLE (row p) ≤ Nat.fromBitsLE (bandEnd width shift p)
  then coefficient (coefficientInput shift p) else []

def entry (a : Access) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (col p) < Nat.fromBitsLE (leftDegree a p)
  then bandEntry a.rightCoefficient (rightDegree a) col p
  else bandEntry a.leftCoefficient (leftDegree a) (rightShift a) p

def dimension (a : Access) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.leftDegree c) (a.rightDegree c))

def dimensionSize (a : Access) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (dimension a c).length

def budget (a : Access) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair
    (BinaryNat.mul (pair (dimensionSize a c) (dimension a c)))
    (BinaryNat.mul (pair (dimension a c) (a.coefficientBits c)))))

theorem row_mem_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_mem_FP : col ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem context_mem_FP : context ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

theorem leftDegree_mem_FP (a : Access) (ha : a.PolyTime) : leftDegree a ∈ FP :=
  mem_FP_comp context_mem_FP ha.leftDegree

theorem rightDegree_mem_FP (a : Access) (ha : a.PolyTime) : rightDegree a ∈ FP :=
  mem_FP_comp context_mem_FP ha.rightDegree

theorem rightShift_mem_FP (a : Access) (ha : a.PolyTime) : rightShift a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair col_mem_FP (leftDegree_mem_FP a ha)) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := rightShift a) h ?_
  intro p
  simp only [Function.comp_apply, rightShift]

theorem coefficientInput_mem_FP {shift : List Bool → List Bool} (hs : shift ∈ FP) :
    coefficientInput shift ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_pair row_mem_FP hs) BinaryNat.sub_mem_FP)
  refine mem_FP_of_eq (g := coefficientInput shift) h ?_
  intro p
  simp only [Function.comp_apply, coefficientInput]

theorem bandEnd_mem_FP {width shift : List Bool → List Bool} (hw : width ∈ FP) (hs : shift ∈ FP) :
    bandEnd width shift ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair hs hw) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := bandEnd width shift) h ?_
  intro p
  simp only [Function.comp_apply, bandEnd]

theorem bandEntry_mem_FP {coefficient width shift : List Bool → List Bool}
    (hc : coefficient ∈ FP) (hw : width ∈ FP) (hs : shift ∈ FP) : bandEntry coefficient width shift ∈ FP := by
  have hlow := BinaryNat.le_fppred hs row_mem_FP
  have hhigh := BinaryNat.le_fppred row_mem_FP (bandEnd_mem_FP hw hs)
  have hread := mem_FP_comp (coefficientInput_mem_FP hs) hc
  have h := (hlow.and hhigh).ite_mem_FP hread (constFn_mem_FP [])
  refine mem_FP_of_eq (g := bandEntry coefficient width shift) h ?_
  intro p
  simp only [Function.comp_apply, bandEntry]

theorem entry_mem_FP (a : Access) (ha : a.PolyTime) : entry a ∈ FP := by
  have hg := BinaryNat.lt_fppred col_mem_FP (leftDegree_mem_FP a ha)
  have hleft := bandEntry_mem_FP ha.rightCoefficient (rightDegree_mem_FP a ha) col_mem_FP
  have hright := bandEntry_mem_FP ha.leftCoefficient (leftDegree_mem_FP a ha) (rightShift_mem_FP a ha)
  have h := hg.ite_mem_FP hleft hright
  refine mem_FP_of_eq (g := entry a) h ?_
  intro p
  simp only [entry]

theorem dimension_mem_FP (a : Access) (ha : a.PolyTime) : dimension a ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.leftDegree ha.rightDegree) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := dimension a) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem dimensionSize_mem_FP (a : Access) (ha : a.PolyTime) : dimensionSize a ∈ FP :=
  bits_mem_FP (UnaryFn.length (dimension_mem_FP a ha))

theorem budget_mem_FP (a : Access) (ha : a.PolyTime) : budget a ∈ FP := by
  have hd := dimension_mem_FP a ha
  have hs := dimensionSize_mem_FP a ha
  have hleft := mem_FP_comp (mem_FP_pair hs hd) BinaryNat.mul_mem_FP
  have hright := mem_FP_comp (mem_FP_pair hd ha.coefficientBits) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hleft hright) BinaryNat.add_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := budget a) h ?_
  intro c
  simp only [Function.comp_apply, budget]

theorem dimension_code (a : Access) (c : List Bool) (m n : ℕ)
    (hm : a.leftDegree c = BinaryNatCode.encode m) (hn : a.rightDegree c = BinaryNatCode.encode n) :
    dimension a c = BinaryNatCode.encode (m + n) := by
  simp only [dimension, hm, hn, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem budget_code (a : Access) (c : List Bool) (m n b : ℕ)
    (hm : a.leftDegree c = BinaryNatCode.encode m) (hn : a.rightDegree c = BinaryNatCode.encode n)
    (hb : a.coefficientBits c = BinaryNatCode.encode b) :
    budget a c = BinaryNatCode.encode ((m + n).size * (m + n) + (m + n) * b + 1) := by
  have hd := dimension_code a c m n hm hn
  simp only [budget, dimensionSize, hd, hb, BinaryNat.add_pair,
    BinaryNat.mul_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.size_eq_bits_len]

end LeanCanny.Algebra.SylvesterBits
