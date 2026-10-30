/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleDouble
public import LeanCanny.Encoding.SquareSampleAccess
public import LeanCanny.Algebra.FixedWidthBlockRenameSpace

/-! # Native coefficient access for paired finite samplers

The selected row chooses a variable block. Existing native block renaming
guards the other block and repacks its monomial for the original reader.
Coordinate annihilators use the original reader directly.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleDouble
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open SquareSampleInput (Inputs source indexWord widthWord rankWord modulusWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def arity (F : Inputs) (q : List Bool) : ℕ := F.count (source q)

def selector (F : Inputs) (q : List Bool) : Fin (arity F q + arity F q) :=
  ⟨min (Nat.fromBitsLE (indexWord q)) (arity F q + arity F q - 1), by
    have := F.count_pos (source q)
    unfold arity
    omega⟩

def rowIndex (F : Inputs) (q : List Bool) : Fin (F.count (source q)) := index (arity F q) (selector F q)
def rowNumber (F : Inputs) (q : List Bool) : ℕ := (rowIndex F q).val
def rowOffset (F : Inputs) (q : List Bool) : ℕ := offset (arity F q) (side (arity F q) (selector F q))

theorem arity_unary {F : Inputs} (hF : F.Access) : UnaryFn (arity F) := hF.count.comp SquareSampleInput.source_FP

theorem selector_unary {F : Inputs} (hF : F.Access) : UnaryFn (fun q => (selector F q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    (((arity_unary hF).add (arity_unary hF)).sub (UnaryFn.const 1))

theorem rowIndex_unary {F : Inputs} (hF : F.Access) : UnaryFn (fun q => (rowIndex F q).val) :=
  UnaryFn.ite (FPPred.lt (selector_unary hF) (arity_unary hF)) (selector_unary hF)
    ((selector_unary hF).sub (arity_unary hF))

theorem rowOffset_unary {F : Inputs} (hF : F.Access) : UnaryFn (rowOffset F) := by
  have H := UnaryFn.ite (FPPred.le (arity_unary hF) (selector_unary hF)) (arity_unary hF) (UnaryFn.const 0)
  exact H.of_eq fun q => by simp only [rowOffset, offset, side, decide_eq_true_eq]

def rowQuery (F : Inputs) (z : List Bool) : List Bool :=
  SquareSampleInput.query (source (LeanCanny.pairFst z)) (BinaryNatCode.encode (rowNumber F (LeanCanny.pairFst z)))
    (widthWord (LeanCanny.pairFst z)) (LeanCanny.pairSnd z) (modulusWord (LeanCanny.pairFst z))

theorem rowQuery_FP {F : Inputs} (hF : F.Access) : rowQuery F ∈ FP :=
  SquareSampleInput.query_FP (mem_FP_comp (f := pairFst) (g := source) pairFst_mem_FP SquareSampleInput.source_FP)
    (BinaryFn.ofUnary ((rowIndex_unary hF).comp pairFst_mem_FP)).bits_mem_FP
    (mem_FP_comp (f := pairFst) (g := widthWord) pairFst_mem_FP SquareSampleInput.widthWord_FP) pairSnd_mem_FP
    (mem_FP_comp (f := pairFst) (g := modulusWord) pairFst_mem_FP SquareSampleInput.modulusWord_FP)

noncomputable def reader (F : Inputs) : List Bool → List Bool := SquareSampleInput.rowCoefficient F ∘ rowQuery F

theorem reader_evaluator {F : Inputs} (hF : F.Access) : SpaceFunction (reader F) :=
  hF.row.precompose (rowQuery F) (rowQuery_FP hF)

theorem reader_packet (F : Inputs) (q : List Bool) (r : ℕ) :
    reader F (LeanCanny.pair q (BinaryNatCode.encode r)) = residueBits
      (((F.system (source q) (rowIndex F q)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (arity F q))) (widthWord q).length r) : ℤ) :
          ZMod (Nat.fromBitsLE (modulusWord q) + 1)) := by
  simp only [reader, Function.comp_apply, rowQuery, pairFst_pair, pairSnd_pair]
  exact (SquareSampleInput.row_packet F (source q) (rowIndex F q) (widthWord q)
    (BinaryNatCode.encode r) (modulusWord q)).trans
      (by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, arity])

noncomputable def rowValue (F : Inputs) : List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (arity F) (fun q => arity F q + arity F q) (rowOffset F)
    (fun q => (widthWord q).length) rankWord (reader F)

theorem rowValue_evaluator {F : Inputs} (hF : F.Access) : SpaceFunction (rowValue F) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _ (reader_evaluator hF)
    (arity_unary hF) ((arity_unary hF).add (arity_unary hF)) (rowOffset_unary hF)
    (UnaryFn.length SquareSampleInput.widthWord_FP) SquareSampleInput.rankWord_FP

theorem rowValue_packet (F : Inputs) (hF : SquareSampleComplete.Complete F) (q : List Bool) :
    rowValue F q = SquareSampleInput.rowCoefficient (input F hF) q := by
  have hfit : rowOffset F q + arity F q ≤ arity F q + arity F q := by
    unfold rowOffset offset
    split_ifs <;> omega
  have H := FixedWidthBlockRenameBits.packet (arity F) (fun q => arity F q + arity F q) (rowOffset F)
    (fun q => (widthWord q).length) rankWord
    (F.system (source q) (rowIndex F q)) hfit (reader F) q (Nat.fromBitsLE (modulusWord q) + 1)
    rfl rfl rfl (reader_packet F q)
  exact H

theorem row_evaluator {F : Inputs} (hF : F.Access) (hC : SquareSampleComplete.Complete F) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input F hC)) :=
  (rowValue_evaluator hF).congr (funext (rowValue_packet F hC))

theorem ann_evaluator {F : Inputs} (hF : F.Access) (hC : SquareSampleComplete.Complete F) :
    SpaceFunction (SquareSampleInput.annCoefficient (input F hC)) :=
  (SquareSampleInput.ann_evaluator hF SquareSampleInput.source_FP (rowIndex F) (rowIndex_unary hF)
    SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP).congr (funext fun _ => rfl)

theorem access {F : Inputs} (hF : F.Access) (hC : SquareSampleComplete.Complete F) : (input F hC).Access :=
  ⟨hF.count.add hF.count, hF.degree, hF.mass, hF.annDegree, hF.annHeight,
    row_evaluator hF hC, ann_evaluator hF hC⟩

end LeanCanny.Encoding.SquareSampleDouble
