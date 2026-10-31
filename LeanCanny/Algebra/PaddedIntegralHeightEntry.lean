/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralHeightSourceMatrix
public import LeanCanny.Algebra.MatrixProductSpace

/-! # Native factors of actual canonical height-numerator matrices

Factor queries retain the original scalar-prefix record and caller
modulus. The new generator is constructed from the original coefficient
reader; the lifted inverse uses binary digit guards and quotient ranks.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralHeightEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCoordinateBasis
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def indices (r : List Bool) : List Bool := pairSnd (pairSnd r)
def rowCode (r : List Bool) : List Bool := pairFst (indices r)
def colCode (r : List Bool) : List Bool := pairSnd (indices r)
def source (r : List Bool) : List Bool := base (pairFst r)
def modulusWord (r : List Bool) : List Bool := modulus (pairFst r)
def factorCode (r : List Bool) : List Bool := pairFst (pairSnd r)
def factor (r : List Bool) : ℕ := Nat.fromBitsLE (factorCode r)

theorem indices_FP : indices ∈ FP := mem_FP_comp (f := pairSnd) (g := pairSnd) pairSnd_mem_FP pairSnd_mem_FP
theorem rowCode_FP : rowCode ∈ FP := mem_FP_comp (f := indices) (g := pairFst) indices_FP pairFst_mem_FP
theorem colCode_FP : colCode ∈ FP := mem_FP_comp (f := indices) (g := pairSnd) indices_FP pairSnd_mem_FP
theorem source_FP : source ∈ FP := mem_FP_comp (f := pairFst) (g := base) pairFst_mem_FP base_FP
theorem modulusWord_FP : modulusWord ∈ FP := mem_FP_comp (f := pairFst) (g := modulus) pairFst_mem_FP modulus_FP
theorem factorCode_FP : factorCode ∈ FP := mem_FP_comp (f := pairSnd) (g := pairFst) pairSnd_mem_FP pairFst_mem_FP
theorem factor_zero_FP : FPPred (fun r => factor r = 0) := (BinaryFn.fromBits factorCode_FP).eq (BinaryFn.const 0)

def radix (S : Source) (r : List Bool) : ℕ := 2 ^ S.width (source r)

theorem radix_binary (S : Source) (a : Access S) : BinaryFn (radix S) :=
  (BinaryFn.const 2).powUnary (a.width.comp source_FP)

def rootQuery (r : List Bool) : List Bool := pair (pair (source r) (modulusWord r)) (indices r)

theorem rootQuery_FP : rootQuery ∈ FP := mem_FP_pair (mem_FP_pair source_FP modulusWord_FP) indices_FP

def oldQuery (S : Source) (r : List Bool) : List Bool :=
  pair (pair (source r) (modulusWord r))
    (pair (BinaryNatCode.encode (Nat.fromBitsLE (rowCode r) / radix S r))
      (BinaryNatCode.encode (Nat.fromBitsLE (colCode r) / radix S r)))

theorem oldQuery_FP (S : Source) (a : Access S) : oldQuery S ∈ FP :=
  mem_FP_pair (mem_FP_pair source_FP modulusWord_FP) (mem_FP_pair
    ((BinaryFn.fromBits rowCode_FP).div (radix_binary S a)).bits_mem_FP
    ((BinaryFn.fromBits colCode_FP).div (radix_binary S a)).bits_mem_FP)

def guard (S : Source) (r : List Bool) : Prop :=
  Nat.fromBitsLE (rowCode r) % radix S r = Nat.fromBitsLE (colCode r) % radix S r

instance (S : Source) : DecidablePred (guard S) := fun r =>
  inferInstanceAs (Decidable (Nat.fromBitsLE (rowCode r) % radix S r = Nat.fromBitsLE (colCode r) % radix S r))

theorem guard_FP (S : Source) (a : Access S) : FPPred (guard S) :=
  ((BinaryFn.fromBits rowCode_FP).mod (radix_binary S a)).eq
    ((BinaryFn.fromBits colCode_FP).mod (radix_binary S a))

noncomputable def liftEntry (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (r : List Bool) : List Bool :=
  if guard S r then PaddedIntegralSelectedMatrixSource.value S B (oldQuery S r) else []

theorem lift_evaluator (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (a : Access S)
    (hh : BinaryFn B.height) (E : SpaceFunction a.entry) : SpaceFunction (liftEntry S B) := by
  have H := SpaceFunction.branch (fun r => decide (guard S r)) (guard_FP S a).flag_mem_FP
    ((PaddedIntegralSelectedMatrixSource.evaluator S B a hh E).precompose (oldQuery S) (oldQuery_FP S a))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun r => by simp only [liftEntry, decide_eq_true_eq, Function.comp_apply])

noncomputable def entry (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (r : List Bool) : List Bool :=
  if factor r = 0 then PaddedIntegralGeneratorSource.value S (rootQuery r) else liftEntry S B r

theorem entry_evaluator (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (a : Access S)
    (hh : BinaryFn B.height) (E : SpaceFunction a.entry) : SpaceFunction (entry S B) := by
  have H := SpaceFunction.branch (fun r => decide (factor r = 0)) factor_zero_FP.flag_mem_FP
    ((PaddedIntegralGeneratorSource.evaluator S a E).precompose rootQuery rootQuery_FP) (lift_evaluator S B a hh E)
  exact H.congr (funext fun r => by simp only [entry, decide_eq_true_eq, Function.comp_apply])

attribute [local irreducible] Source.matrix PaddedIntegralSelectedMatrixSource.matrix

theorem root_packet (S : Source) (q : List Bool) (k : ℕ) (i j : Fin (rank S q)) :
    PaddedIntegralGeneratorSource.value S
      (rootQuery (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))))) =
      residueBits ((S.matrix (base q) i j : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  simp only [rootQuery, source, modulusWord, indices, pairFst_pair, pairSnd_pair]
  exact PaddedIntegralGeneratorSource.value_packet S (base q) (modulus q) i j

theorem old_query_packet (S : Source) (q : List Bool) (k : ℕ) (i j : Fin (rank S q)) :
    oldQuery S (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      pair (pair (base q) (modulus q))
        (pair (BinaryNatCode.encode ((pairIndex (S.arity (base q)) (S.width (base q))).symm i).1.val)
          (BinaryNatCode.encode ((pairIndex (S.arity (base q)) (S.width (base q))).symm j).1.val)) := by
  simp only [oldQuery, source, modulusWord, rowCode, colCode, indices, radix, pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode i.val) = i.val from Nat.fromBitsLE_bits _,
    show Nat.fromBitsLE (BinaryNatCode.encode j.val) = j.val from Nat.fromBitsLE_bits _]
  rfl

theorem guard_packet (S : Source) (q : List Bool) (k : ℕ) (i j : Fin (rank S q)) :
    guard S (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) ↔
      ((pairIndex (S.arity (base q)) (S.width (base q))).symm i).2 =
        ((pairIndex (S.arity (base q)) (S.width (base q))).symm j).2 := by
  simp only [guard, rowCode, colCode, indices, radix, source, pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode i.val) = i.val from Nat.fromBitsLE_bits _,
    show Nat.fromBitsLE (BinaryNatCode.encode j.val) = j.val from Nat.fromBitsLE_bits _]
  exact (show ((pairIndex (S.arity (base q)) (S.width (base q))).symm i).2 =
      ((pairIndex (S.arity (base q)) (S.width (base q))).symm j).2 ↔
      (((pairIndex (S.arity (base q)) (S.width (base q))).symm i).2).val =
      (((pairIndex (S.arity (base q)) (S.width (base q))).symm j).2).val from Fin.ext_iff).symm

theorem lift_packet (S : Source) (B : PaddedIntegralSelectedMatrixSource.Bounds S) (q : List Bool) (k : ℕ)
    (i j : Fin (rank S q)) :
    liftEntry S B (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((PaddedIntegralHeightSourceMatrix.liftMatrix S (base q) i j : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  rw [liftEntry]
  by_cases h : ((pairIndex (S.arity (base q)) (S.width (base q))).symm i).2 =
      ((pairIndex (S.arity (base q)) (S.width (base q))).symm j).2
  · rw [ite_eq_left ((guard_packet S q k i j).mpr h), old_query_packet,
      PaddedIntegralSelectedMatrixSource.value_packet]
    simp only [PaddedIntegralHeightSourceMatrix.liftMatrix, h, ite_true]
  · rw [ite_eq_right (fun hg => h ((guard_packet S q k i j).mp hg))]
    simp only [PaddedIntegralHeightSourceMatrix.liftMatrix, h, ite_false, Int.cast_zero,
      residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]

end LeanCanny.Algebra.PaddedIntegralHeightEntryBits
