/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Algebra.BerkowitzFactorAccess
public import LeanCanny.Algebra.MatrixMomentFP

/-!
# Binary fields and case selection for layered determinant queries

An entry request is `pair context (pair rowIndex colIndex)`. Dividing each
flattened index by the binary width n+1 recovers its layer and coefficient
index. Truncated subtraction writes the trailing-block dimension and the
moment exponent. All operations and the four-case selector are FP on all
strings; numeric specifications include malformed and noncanonical words.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.QueryBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets

def inputDimension (dim : List Bool → List Bool) (p : List Bool) : List Bool := dim (pairFst p)
def rowIndex (p : List Bool) : List Bool := pairFst (pairSnd p)
def colIndex (p : List Bool) : List Bool := pairSnd (pairSnd p)
def width (dim : List Bool → List Bool) (p : List Bool) : List Bool := BinaryNat.succ (inputDimension dim p)
def splitIndex (dim index : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.divMod (pair (index p) (width dim p))
def sourceLayer (dim : List Bool → List Bool) : List Bool → List Bool := pairFst ∘ splitIndex dim rowIndex
def targetLayer (dim : List Bool → List Bool) : List Bool → List Bool := pairFst ∘ splitIndex dim colIndex
def sourceDegree (dim : List Bool → List Bool) : List Bool → List Bool := pairSnd ∘ splitIndex dim rowIndex
def targetDegree (dim : List Bool → List Bool) : List Bool → List Bool := pairSnd ∘ splitIndex dim colIndex
def remaining (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.pred (BinaryNat.sub (pair (inputDimension dim p) (sourceLayer dim p)))
def offset (dim : List Bool → List Bool) (p : List Bool) : List Bool := BinaryNat.succ (sourceLayer dim p)
def momentExponent (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  BinaryNat.sub (pair (targetDegree dim p) (BinaryNat.succ (sourceDegree dim p)))

theorem inputDimension_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : inputDimension dim ∈ FP :=
  mem_FP_comp pairFst_mem_FP hd
theorem rowIndex_mem_FP : rowIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem colIndex_mem_FP : colIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem width_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : width dim ∈ FP :=
  mem_FP_comp (inputDimension_mem_FP hd) BinaryNat.succ_mem_FP

theorem splitIndex_mem_FP {dim index : List Bool → List Bool} (hd : dim ∈ FP) (hi : index ∈ FP) :
    splitIndex dim index ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair hi (width_mem_FP hd)) BinaryNat.divMod_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem sourceLayer_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : sourceLayer dim ∈ FP :=
  mem_FP_comp (splitIndex_mem_FP hd rowIndex_mem_FP) pairFst_mem_FP
theorem targetLayer_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : targetLayer dim ∈ FP :=
  mem_FP_comp (splitIndex_mem_FP hd colIndex_mem_FP) pairFst_mem_FP
theorem sourceDegree_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : sourceDegree dim ∈ FP :=
  mem_FP_comp (splitIndex_mem_FP hd rowIndex_mem_FP) pairSnd_mem_FP
theorem targetDegree_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : targetDegree dim ∈ FP :=
  mem_FP_comp (splitIndex_mem_FP hd colIndex_mem_FP) pairSnd_mem_FP

theorem remaining_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : remaining dim ∈ FP := by
  have hs := mem_FP_comp (mem_FP_pair (inputDimension_mem_FP hd) (sourceLayer_mem_FP hd)) BinaryNat.sub_mem_FP
  have h := mem_FP_comp hs BinaryNat.pred_mem_FP
  refine mem_FP_of_eq (g := remaining dim) h ?_
  intro p
  simp only [Function.comp_apply, remaining]

theorem offset_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : offset dim ∈ FP :=
  mem_FP_comp (sourceLayer_mem_FP hd) BinaryNat.succ_mem_FP

theorem momentExponent_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : momentExponent dim ∈ FP := by
  have hsucc := mem_FP_comp (sourceDegree_mem_FP hd) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair (targetDegree_mem_FP hd) hsucc) BinaryNat.sub_mem_FP
  refine mem_FP_of_eq (g := momentExponent dim) h ?_
  intro p
  simp only [Function.comp_apply, momentExponent]

theorem code_value (b : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode b) = b := Nat.fromBitsLE_bits b

theorem splitIndex_eq_code (dim index : List Bool → List Bool) (p : List Bool) :
    splitIndex dim index p =
      pair (BinaryNatCode.encode (Nat.fromBitsLE (index p) / (Nat.fromBitsLE (inputDimension dim p) + 1)))
        (BinaryNatCode.encode (Nat.fromBitsLE (index p) % (Nat.fromBitsLE (inputDimension dim p) + 1))) := by
  simp only [splitIndex, width, BinaryNat.divMod_pair, BinaryNat.succ_eq_bits,
    Nat.fromBitsLE_bits, BinaryNatCode.encode]

theorem sourceLayer_eq_code (dim : List Bool → List Bool) (p : List Bool) : sourceLayer dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (rowIndex p) / (Nat.fromBitsLE (inputDimension dim p) + 1)) := by
  simp only [sourceLayer, Function.comp_apply, splitIndex_eq_code, pairFst_pair]
theorem targetLayer_eq_code (dim : List Bool → List Bool) (p : List Bool) : targetLayer dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (colIndex p) / (Nat.fromBitsLE (inputDimension dim p) + 1)) := by
  simp only [targetLayer, Function.comp_apply, splitIndex_eq_code, pairFst_pair]
theorem sourceDegree_eq_code (dim : List Bool → List Bool) (p : List Bool) : sourceDegree dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (rowIndex p) % (Nat.fromBitsLE (inputDimension dim p) + 1)) := by
  simp only [sourceDegree, Function.comp_apply, splitIndex_eq_code, pairSnd_pair]
theorem targetDegree_eq_code (dim : List Bool → List Bool) (p : List Bool) : targetDegree dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (colIndex p) % (Nat.fromBitsLE (inputDimension dim p) + 1)) := by
  simp only [targetDegree, Function.comp_apply, splitIndex_eq_code, pairSnd_pair]

theorem remaining_eq_code (dim : List Bool → List Bool) (p : List Bool) : remaining dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (inputDimension dim p) -
      Nat.fromBitsLE (rowIndex p) / (Nat.fromBitsLE (inputDimension dim p) + 1) - 1) := by
  simp only [remaining, sourceLayer_eq_code, BinaryNat.sub_pair, BinaryNat.pred_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem offset_eq_code (dim : List Bool → List Bool) (p : List Bool) : offset dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (rowIndex p) / (Nat.fromBitsLE (inputDimension dim p) + 1) + 1) := by
  simp only [offset, sourceLayer_eq_code, MatrixMoment.EntryBits.succ_code]

theorem momentExponent_eq_code (dim : List Bool → List Bool) (p : List Bool) : momentExponent dim p =
    BinaryNatCode.encode (Nat.fromBitsLE (colIndex p) % (Nat.fromBitsLE (inputDimension dim p) + 1) -
      (Nat.fromBitsLE (rowIndex p) % (Nat.fromBitsLE (inputDimension dim p) + 1) + 1)) := by
  simp only [momentExponent, targetDegree_eq_code, sourceDegree_eq_code,
    BinaryNat.succ_eq_bits, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

/-- Codes: zero `[]`, one `[true]`, diagonal `[false,true]`, moment `[true,true]`. -/
def selector (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  if BinaryNat.succ (sourceLayer dim p) = targetLayer dim p then
    if Nat.fromBitsLE (sourceLayer dim p) < Nat.fromBitsLE (inputDimension dim p) then
      if BinaryNat.succ (targetDegree dim p) = sourceDegree dim p then [true]
      else if targetDegree dim p = sourceDegree dim p then [false, true]
      else if Nat.fromBitsLE (sourceDegree dim p) < Nat.fromBitsLE (targetDegree dim p) then
        if Nat.fromBitsLE (targetDegree dim p) ≤ Nat.fromBitsLE (remaining dim p) then [true, true] else []
      else []
    else []
  else []

theorem selector_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : selector dim ∈ FP := by
  have hs := sourceLayer_mem_FP hd
  have ht := targetLayer_mem_FP hd
  have hdg := sourceDegree_mem_FP hd
  have hkg := targetDegree_mem_FP hd
  have hn := inputDimension_mem_FP hd
  have hb := remaining_mem_FP hd
  have hedge := stringEq_fppred (mem_FP_comp hs BinaryNat.succ_mem_FP) ht
  have hshift := stringEq_fppred (mem_FP_comp hkg BinaryNat.succ_mem_FP) hdg
  have hdiag := stringEq_fppred hkg hdg
  have hz := constFn_mem_FP ([] : List Bool)
  have hm := (BinaryNat.lt_fppred hdg hkg).ite_mem_FP
    ((BinaryNat.le_fppred hkg hb).ite_mem_FP (constFn_mem_FP [true, true]) hz) hz
  have hcase := hshift.ite_mem_FP (constFn_mem_FP [true])
    (hdiag.ite_mem_FP (constFn_mem_FP [false, true]) hm)
  have h := hedge.ite_mem_FP ((BinaryNat.lt_fppred hs hn).ite_mem_FP hcase hz) hz
  exact mem_FP_of_eq h (fun _ => rfl)

def select (N s t d k : ℕ) : List Bool :=
  if s + 1 = t then
    if s < N then
      if k + 1 = d then [true]
      else if k = d then [false, true]
      else if d < k then if k ≤ N - s - 1 then [true, true] else [] else []
    else []
  else []

theorem select_one_iff (N s t d k : ℕ) : select N s t d k = [true] ↔
    s + 1 = t ∧ s < N ∧ k + 1 = d := by
  unfold select
  split_ifs <;> simp_all

theorem select_diagonal_iff (N s t d k : ℕ) : select N s t d k = [false, true] ↔
    s + 1 = t ∧ s < N ∧ k = d := by
  unfold select
  split_ifs <;> simp_all
  omega

theorem select_moment_iff (N s t d k : ℕ) : select N s t d k = [true, true] ↔
    s + 1 = t ∧ s < N ∧ d < k ∧ k ≤ N - s - 1 := by
  unfold select
  split_ifs <;> simp_all
  omega

theorem selector_eq_select (dim : List Bool → List Bool) (p : List Bool) :
    selector dim p = select (Nat.fromBitsLE (inputDimension dim p))
      (Nat.fromBitsLE (rowIndex p) / (Nat.fromBitsLE (inputDimension dim p) + 1))
      (Nat.fromBitsLE (colIndex p) / (Nat.fromBitsLE (inputDimension dim p) + 1))
      (Nat.fromBitsLE (rowIndex p) % (Nat.fromBitsLE (inputDimension dim p) + 1))
      (Nat.fromBitsLE (colIndex p) % (Nat.fromBitsLE (inputDimension dim p) + 1)) := by
  simp only [selector, select, sourceLayer_eq_code, targetLayer_eq_code, sourceDegree_eq_code,
    targetDegree_eq_code, remaining_eq_code, MatrixMoment.EntryBits.succ_code,
    BinaryNatCode.encode_injective.eq_iff, code_value]

theorem sourceLayer_packet (dim : List Bool → List Bool) (c : List Bool) (n i j : ℕ)
    (hd : dim c = BinaryNatCode.encode n) :
    sourceLayer dim (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      BinaryNatCode.encode (i / (n + 1)) := by
  simp only [sourceLayer_eq_code, inputDimension, rowIndex, pairFst_pair, pairSnd_pair, hd, code_value]

theorem targetLayer_packet (dim : List Bool → List Bool) (c : List Bool) (n i j : ℕ)
    (hd : dim c = BinaryNatCode.encode n) :
    targetLayer dim (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      BinaryNatCode.encode (j / (n + 1)) := by
  simp only [targetLayer_eq_code, inputDimension, colIndex, pairFst_pair, pairSnd_pair, hd, code_value]

theorem sourceDegree_packet (dim : List Bool → List Bool) (c : List Bool) (n i j : ℕ)
    (hd : dim c = BinaryNatCode.encode n) :
    sourceDegree dim (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      BinaryNatCode.encode (i % (n + 1)) := by
  simp only [sourceDegree_eq_code, inputDimension, rowIndex, pairFst_pair, pairSnd_pair, hd, code_value]

theorem targetDegree_packet (dim : List Bool → List Bool) (c : List Bool) (n i j : ℕ)
    (hd : dim c = BinaryNatCode.encode n) :
    targetDegree dim (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      BinaryNatCode.encode (j % (n + 1)) := by
  simp only [targetDegree_eq_code, inputDimension, colIndex, pairFst_pair, pairSnd_pair, hd, code_value]

theorem selector_packet (dim : List Bool → List Bool) (c : List Bool) (n i j : ℕ)
    (hd : dim c = BinaryNatCode.encode n) :
    selector dim (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      select n (i / (n + 1)) (j / (n + 1)) (i % (n + 1)) (j % (n + 1)) := by
  simp only [selector_eq_select, inputDimension, rowIndex, colIndex,
    pairFst_pair, pairSnd_pair, hd, code_value]

end LeanCanny.Algebra.Berkowitz.QueryBits
