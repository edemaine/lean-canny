/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantMinor
public import LeanCanny.Algebra.SylvesterPolynomialSpace

/-!
# Binary access to subresultant minor coefficients

FP field writers supply the subresultant order and selected coefficient.
The query transformation changes only the matrix row and column, retaining
the original context and parameter-coefficient degree for the existing
space-bounded Sylvester-entry routine.
-/

@[expose] public section

namespace LeanCanny.Algebra.SubresultantBits

open LeanCanny.Encoding
open LeanCanny.Computation

structure Access where
  base : SylvesterPolynomialBits.Access
  order : List Bool → List Bool
  coefficient : List Bool → List Bool

structure Access.ControlsPolyTime (a : Access) : Prop where
  base : a.base.ControlsPolyTime
  order : a.order ∈ FP
  coefficient : a.coefficient ∈ FP

namespace Access

def row (p : List Bool) : List Bool := pairFst (pairSnd p)
def col (p : List Bool) : List Bool := pairFst (pairSnd (pairSnd p))
def degree (p : List Bool) : List Bool := pairSnd (pairSnd (pairSnd p))
def leftWidth (a : Access) (c : List Bool) : List Bool := BinaryNat.sub (pair (a.base.leftDegree c) (a.order c))
def rightWidth (a : Access) (c : List Bool) : List Bool := BinaryNat.sub (pair (a.base.rightDegree c) (a.order c))
def dimension (a : Access) (c : List Bool) : List Bool := BinaryNat.add (pair (a.leftWidth c) (a.rightWidth c))
def selectedRow (a : Access) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (row p) = 0 then a.coefficient (pairFst p) else BinaryNat.add (pair (a.order (pairFst p)) (row p))
def selectedCol (a : Access) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (col p) < Nat.fromBitsLE (a.leftWidth (pairFst p)) then col p
  else BinaryNat.add (pair (col p) (a.order (pairFst p)))
def query (a : Access) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (a.selectedRow p) (pair (a.selectedCol p) (degree p)))
def enabled (a : Access) (c : List Bool) : Prop :=
  Nat.fromBitsLE (a.order c) < Nat.fromBitsLE (a.base.leftDegree c) ∧
    Nat.fromBitsLE (a.order c) < Nat.fromBitsLE (a.base.rightDegree c) ∧
    Nat.fromBitsLE (a.coefficient c) ≤ Nat.fromBitsLE (a.order c)
instance (a : Access) (c : List Bool) : Decidable (a.enabled c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem row_mem_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_mem_FP : col ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem degree_mem_FP : degree ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem leftWidth_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.leftWidth ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.base.leftDegree ha.order) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := a.leftWidth) h ?_
  intro c
  simp only [Function.comp_apply, leftWidth]
theorem rightWidth_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.rightWidth ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.base.rightDegree ha.order) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := a.rightWidth) h ?_
  intro c
  simp only [Function.comp_apply, rightWidth]
theorem dimension_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.dimension ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (leftWidth_mem_FP a ha) (rightWidth_mem_FP a ha)) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.dimension) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem selectedRow_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.selectedRow ∈ FP := by
  have hz := (BinaryNat.lt_fppred row_mem_FP (constFn_mem_FP [true])).of_iff
    (fun p => by change Nat.fromBitsLE (row p) < 1 ↔ Nat.fromBitsLE (row p) = 0; omega)
  have hk := mem_FP_comp pairFst_mem_FP ha.order
  have hr := mem_FP_comp pairFst_mem_FP ha.coefficient
  have hs := mem_FP_comp (mem_FP_pair hk row_mem_FP) BinaryNat.add_mem_FP
  have h := hz.ite_mem_FP hr hs
  refine mem_FP_of_eq (g := a.selectedRow) h ?_
  intro p
  simp only [Function.comp_apply, selectedRow]

theorem selectedCol_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.selectedCol ∈ FP := by
  have hw := mem_FP_comp pairFst_mem_FP (leftWidth_mem_FP a ha)
  have hk := mem_FP_comp pairFst_mem_FP ha.order
  have hs := mem_FP_comp (mem_FP_pair col_mem_FP hk) BinaryNat.add_mem_FP
  have h := (BinaryNat.lt_fppred col_mem_FP hw).ite_mem_FP col_mem_FP hs
  refine mem_FP_of_eq (g := a.selectedCol) h ?_
  intro p
  simp only [Function.comp_apply, selectedCol]

theorem query_mem_FP (a : Access) (ha : a.ControlsPolyTime) : a.query ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair (selectedRow_mem_FP a ha)
    (mem_FP_pair (selectedCol_mem_FP a ha) degree_mem_FP))
  refine mem_FP_of_eq (g := a.query) h ?_
  intro p
  simp only [query]

theorem enabled_fppred (a : Access) (ha : a.ControlsPolyTime) : FPPred a.enabled :=
  (BinaryNat.lt_fppred ha.order ha.base.leftDegree).and
    ((BinaryNat.lt_fppred ha.order ha.base.rightDegree).and (BinaryNat.le_fppred ha.coefficient ha.order))

theorem dimension_code (a : Access) (c : List Bool) (m n k : ℕ)
    (hm : a.base.leftDegree c = BinaryNatCode.encode m) (hn : a.base.rightDegree c = BinaryNatCode.encode n)
    (hk : a.order c = BinaryNatCode.encode k) : a.dimension c = BinaryNatCode.encode ((m - k) + (n - k)) := by
  simp only [dimension, leftWidth, rightWidth, hm, hn, hk, BinaryNat.sub_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem query_packet (a : Access) (c : List Bool) (m k r i j d : ℕ)
    (hm : a.base.leftDegree c = BinaryNatCode.encode m) (hk : a.order c = BinaryNatCode.encode k)
    (hr : a.coefficient c = BinaryNatCode.encode r) :
    a.query (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode j) (BinaryNatCode.encode d)))) =
      pair c (pair (BinaryNatCode.encode (Subresultant.rowIndex k r i))
        (pair (BinaryNatCode.encode (Subresultant.colIndex m k j)) (BinaryNatCode.encode d))) := by
  simp only [query, selectedRow, selectedCol, row, col, degree, pairFst_pair, pairSnd_pair,
    leftWidth, hm, hk, hr, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Subresultant.rowIndex, Subresultant.colIndex]
  split_ifs <;> simp only [BinaryNat.add_pair, Nat.fromBitsLE_bits]

end Access
end LeanCanny.Algebra.SubresultantBits
