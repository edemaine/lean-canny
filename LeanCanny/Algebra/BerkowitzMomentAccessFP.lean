/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzQueryFP

/-!
# Certified access to the trailing block for a factor's moment child

The child context is the original layered entry request. Its vector and matrix
queries add the decoded stage offset to their binary indices and call the
original input matrix accessor. These writers are FP, and their contracts
identify exactly the row, column, and smaller matrix in the factor formula.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.EntryAccess

open LeanCanny.Encoding
open QueryBits
open MatrixPower

def diagonalInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (sourceLayer dim p) (sourceLayer dim p))

def rowInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  let q := pairFst p
  pair (pairFst q) (pair (sourceLayer dim q) (BinaryNat.add (pair (offset dim q) (pairSnd p))))

def columnInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  let q := pairFst p
  pair (pairFst q) (pair (BinaryNat.add (pair (offset dim q) (pairSnd p))) (sourceLayer dim q))

def matrixInput (dim : List Bool → List Bool) (p : List Bool) : List Bool :=
  let q := pairFst p
  let indices := pairSnd p
  pair (pairFst q) (pair (BinaryNat.add (pair (offset dim q) (pairFst indices)))
    (BinaryNat.add (pair (offset dim q) (pairSnd indices))))

theorem diagonalInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : diagonalInput dim ∈ FP := by
  have hs := sourceLayer_mem_FP hd
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair hs hs)
  refine mem_FP_of_eq (g := diagonalInput dim) h ?_
  intro p
  simp only [diagonalInput]

theorem rowInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : rowInput dim ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP (sourceLayer_mem_FP hd)
  have ho := mem_FP_comp pairFst_mem_FP (offset_mem_FP hd)
  have hj := mem_FP_comp (mem_FP_pair ho pairSnd_mem_FP) BinaryNat.add_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hs hj)
  refine mem_FP_of_eq (g := rowInput dim) h ?_
  intro p
  simp only [Function.comp_apply, rowInput]

theorem columnInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : columnInput dim ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp pairFst_mem_FP (sourceLayer_mem_FP hd)
  have ho := mem_FP_comp pairFst_mem_FP (offset_mem_FP hd)
  have hi := mem_FP_comp (mem_FP_pair ho pairSnd_mem_FP) BinaryNat.add_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hi hs)
  refine mem_FP_of_eq (g := columnInput dim) h ?_
  intro p
  simp only [Function.comp_apply, columnInput]

theorem matrixInput_mem_FP {dim : List Bool → List Bool} (hd : dim ∈ FP) : matrixInput dim ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have ho := mem_FP_comp pairFst_mem_FP (offset_mem_FP hd)
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hj := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hrow := mem_FP_comp (mem_FP_pair ho hi) BinaryNat.add_mem_FP
  have hcol := mem_FP_comp (mem_FP_pair ho hj) BinaryNat.add_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hrow hcol)
  refine mem_FP_of_eq (g := matrixInput dim) h ?_
  intro p
  simp only [Function.comp_apply, matrixInput]

theorem diagonalInput_code (dim : List Bool → List Bool) (p : List Bool) (s : ℕ)
    (hs : sourceLayer dim p = BinaryNatCode.encode s) :
    diagonalInput dim p = pair (pairFst p) (pair (BinaryNatCode.encode s) (BinaryNatCode.encode s)) := by
  simp only [diagonalInput, hs]

theorem rowInput_code (dim : List Bool → List Bool) (p : List Bool) (s j : ℕ)
    (hs : sourceLayer dim p = BinaryNatCode.encode s) :
    rowInput dim (pair p (BinaryNatCode.encode j)) =
      pair (pairFst p) (pair (BinaryNatCode.encode s) (BinaryNatCode.encode (s + 1 + j))) := by
  simp only [rowInput, pairFst_pair, pairSnd_pair, offset, hs, BinaryNat.succ_eq_bits,
    BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem columnInput_code (dim : List Bool → List Bool) (p : List Bool) (s i : ℕ)
    (hs : sourceLayer dim p = BinaryNatCode.encode s) :
    columnInput dim (pair p (BinaryNatCode.encode i)) =
      pair (pairFst p) (pair (BinaryNatCode.encode (s + 1 + i)) (BinaryNatCode.encode s)) := by
  simp only [columnInput, pairFst_pair, pairSnd_pair, offset, hs, BinaryNat.succ_eq_bits,
    BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem matrixInput_code (dim : List Bool → List Bool) (p : List Bool) (s i j : ℕ)
    (hs : sourceLayer dim p = BinaryNatCode.encode s) :
    matrixInput dim (pair p (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      pair (pairFst p) (pair (BinaryNatCode.encode (s + 1 + i)) (BinaryNatCode.encode (s + 1 + j))) := by
  simp only [matrixInput, pairFst_pair, pairSnd_pair, offset, hs, BinaryNat.succ_eq_bits,
    BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def momentAccess (dim entry : List Bool → List Bool) : MatrixMoment.EntryBits.Access where
  dimension := remaining dim
  row := entry ∘ rowInput dim
  column := entry ∘ columnInput dim
  entry := entry ∘ matrixInput dim

theorem momentAccess_polyTime {dim entry : List Bool → List Bool} (hd : dim ∈ FP) (he : entry ∈ FP) :
    (momentAccess dim entry).PolyTime := by
  have hr := mem_FP_comp (rowInput_mem_FP hd) he
  have hc := mem_FP_comp (columnInput_mem_FP hd) he
  have hm := mem_FP_comp (matrixInput_mem_FP hd) he
  exact ⟨remaining_mem_FP hd, hr, hc, hm⟩

def childModulus (modulus : List Bool → List Bool) : List Bool → List Bool := modulus ∘ pairFst

theorem childModulus_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    childModulus modulus ∈ FP := mem_FP_comp pairFst_mem_FP hm

theorem momentCallbacks_polyTime {dim entry modulus : List Bool → List Bool}
    (hd : dim ∈ FP) (he : entry ∈ FP) (hm : modulus ∈ FP) :
    (MatrixMoment.EntryBits.callbacks (momentAccess dim entry) (childModulus modulus)).PolyTime :=
  MatrixMoment.EntryBits.callbacks_polyTime _ (momentAccess_polyTime hd he) (childModulus_mem_FP hm)

theorem momentStart_mem_FP {dim entry : List Bool → List Bool} (hd : dim ∈ FP) (he : entry ∈ FP) :
    MatrixMoment.EntryBits.start (momentAccess dim entry) (momentExponent dim) ∈ FP :=
  MatrixMoment.EntryBits.start_mem_FP _ (momentAccess_polyTime hd he) (momentExponent_mem_FP hd)

theorem momentCallbacks_correctAt (dim entry modulus : List Bool → List Bool)
    (p : List Bool) (m n s : ℕ) [NeZero m] (A : Matrix (Fin n) (Fin n) (ZMod m)) (hs : s < n)
    (hd : dim (pairFst p) = BinaryNatCode.encode n)
    (hl : sourceLayer dim p = BinaryNatCode.encode s)
    (hm : modulus (pairFst p) = BinaryNatCode.encode m)
    (he : ∀ i j, entry (pair (pairFst p) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (A i j)) :
    Controller.CorrectAt (MatrixMoment.EntryBits.callbacks (momentAccess dim entry) (childModulus modulus))
      p (factorMomentMatrix A s hs) residueBits := by
  dsimp only [factorMomentMatrix]
  apply MatrixMoment.EntryBits.callbacks_correctAt
  · simp only [momentAccess, remaining, inputDimension, hd, hl, BinaryNat.sub_pair,
      BinaryNat.pred_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · exact hm
  · intro j
    simp only [momentAccess, Function.comp_apply, rowInput_code dim p s j.val hl]
    have h := he ⟨s, hs⟩ ⟨s + 1 + j.val, by have := j.isLt; omega⟩
    simpa [principalBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · intro i
    simp only [momentAccess, Function.comp_apply, columnInput_code dim p s i.val hl]
    have h := he ⟨s + 1 + i.val, by have := i.isLt; omega⟩ ⟨s, hs⟩
    simpa [principalBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  · intro i j
    simp only [momentAccess, Function.comp_apply, matrixInput_code dim p s i.val j.val hl]
    have h := he ⟨s + 1 + i.val, by have := i.isLt; omega⟩
      ⟨s + 1 + j.val, by have := j.isLt; omega⟩
    simpa [principalBlock, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end LeanCanny.Algebra.Berkowitz.EntryAccess
