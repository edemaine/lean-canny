/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixMomentFP
public import LeanCanny.Algebra.MatrixPowerSpaceEntries
public import LeanCanny.Computation.SpaceFunctionBranch

/-!
# Scalar moments with space-bounded vector and matrix access

FP guards choose a row, column, original matrix entry, or zero in the augmented
matrix. The selected data routine may use polynomial space. Modular powering
then computes the complete scalar moment with all child states accounted for.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixMoment.EntryBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

def rowInput (p : List Bool) : List Bool := pair (pairFst p) (BinaryNat.pred (colIndex p))
def columnInput (p : List Bool) : List Bool := pair (pairFst p) (BinaryNat.pred (rowIndex p))
def matrixInput (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (BinaryNat.pred (rowIndex p)) (BinaryNat.pred (colIndex p)))

theorem rowInput_mem_FP : rowInput ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp colIndex_mem_FP BinaryNat.pred_mem_FP)
  refine mem_FP_of_eq (g := rowInput) h ?_
  intro p
  simp only [Function.comp_apply, rowInput]

theorem columnInput_mem_FP : columnInput ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp rowIndex_mem_FP BinaryNat.pred_mem_FP)
  refine mem_FP_of_eq (g := columnInput) h ?_
  intro p
  simp only [Function.comp_apply, columnInput]

theorem matrixInput_mem_FP : matrixInput ∈ FP := by
  have hi := mem_FP_comp rowIndex_mem_FP BinaryNat.pred_mem_FP
  have hj := mem_FP_comp colIndex_mem_FP BinaryNat.pred_mem_FP
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_pair hi hj)
  refine mem_FP_of_eq (g := matrixInput) h ?_
  intro p
  simp only [Function.comp_apply, matrixInput]

theorem sinkIndex_mem_FP_of_dimension (a : Access) (hd : a.dimension ∈ FP) : sinkIndex a ∈ FP := by
  have h := mem_FP_comp hd BinaryNat.succ_mem_FP
  exact h

theorem dimension_mem_FP_of_dimension (a : Access) (hd : a.dimension ∈ FP) : dimension a ∈ FP := by
  have h := mem_FP_comp (sinkIndex_mem_FP_of_dimension a hd) BinaryNat.succ_mem_FP
  exact h

theorem entryEvaluator (a : Access) (hd : a.dimension ∈ FP)
    (R : SpaceFunction a.row) (C : SpaceFunction a.column) (A : SpaceFunction a.entry) :
    SpaceFunction (entry a) := by
  have ER := R.precompose rowInput rowInput_mem_FP
  have EC := C.precompose columnInput columnInput_mem_FP
  have EA := A.precompose matrixInput matrixInput_mem_FP
  let Z := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have hz := constFn_mem_FP ([] : List Bool)
  have hl := mem_FP_comp pairFst_mem_FP (sinkIndex_mem_FP_of_dimension a hd)
  have hrow0 := (stringEq_fppred rowIndex_mem_FP hz).flag_mem_FP
  have hcol0 := (stringEq_fppred colIndex_mem_FP hz).flag_mem_FP
  have hrowLast := (stringEq_fppred rowIndex_mem_FP hl).flag_mem_FP
  have hcolLast := (stringEq_fppred colIndex_mem_FP hl).flag_mem_FP
  have ErowLast := SpaceFunction.branch (fun p => decide (colIndex p = sinkIndex a (pairFst p))) hcolLast Z ER
  have Erow := SpaceFunction.branch (fun p => decide (colIndex p = [])) hcol0 Z ErowLast
  have EbodyLast := SpaceFunction.branch (fun p => decide (colIndex p = sinkIndex a (pairFst p))) hcolLast EC EA
  have Ebody0 := SpaceFunction.branch (fun p => decide (colIndex p = [])) hcol0 Z EbodyLast
  have Ebody := SpaceFunction.branch (fun p => decide (rowIndex p = sinkIndex a (pairFst p))) hrowLast Z Ebody0
  have E := SpaceFunction.branch (fun p => decide (rowIndex p = [])) hrow0 Erow Ebody
  refine E.congr ?_
  funext p
  simp only [entry, rowInput, columnInput, matrixInput, Function.comp_apply, decide_eq_true_eq]

end LeanCanny.Algebra.MatrixMoment.EntryBits

namespace LeanCanny.Algebra.MatrixMoment
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open Matrix

structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  exponent : List Bool → ℕ
  row : (c : List Bool) → Fin (dimension c) → ZMod (modulus c)
  column : (c : List Bool) → Fin (dimension c) → ZMod (modulus c)
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits (F.row c ⬝ᵥ (F.matrix c ^ F.exponent c *ᵥ F.column c))

def ModularFamily.power (F : ModularFamily) : MatrixPower.ModularFamily where
  dimension := fun c => F.dimension c + 2
  modulus := F.modulus
  exponent := fun c => F.exponent c + 2
  row := fun _ => 0
  col := fun c => Fin.last (F.dimension c + 1)
  matrix := fun c => matrixFin (F.row c) (F.column c) (F.matrix c)
  modulus_ne_zero := F.modulus_ne_zero

structure ModularAccess (F : ModularFamily) where
  bits : EntryBits.Access
  modulus : List Bool → List Bool
  exponent : List Bool → List Bool
  dimension_eq : ∀ c, bits.dimension c = BinaryNatCode.encode (F.dimension c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  exponent_eq : ∀ c, exponent c = BinaryNatCode.encode (F.exponent c)
  row_eq : ∀ c j, bits.row (pair c (BinaryNatCode.encode j.val)) = residueBits (F.row c j)
  column_eq : ∀ c i, bits.column (pair c (BinaryNatCode.encode i.val)) = residueBits (F.column c i)
  entry_eq : ∀ c i j, bits.entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
    residueBits (F.matrix c i j)

structure ModularAccess.ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.bits.dimension ∈ FP
  modulus : a.modulus ∈ FP
  exponent : a.exponent ∈ FP

namespace ModularAccess

def power {F : ModularFamily} (a : ModularAccess F) : MatrixPower.ModularAccess F.power where
  dimension := EntryBits.dimension a.bits
  modulus := a.modulus
  exponent := fun c => Encoding.BinaryNat.succ (Encoding.BinaryNat.succ (a.exponent c))
  row := fun _ => []
  col := EntryBits.sinkIndex a.bits
  entry := EntryBits.entry a.bits
  dimension_eq := fun c => by simp [EntryBits.dimension, EntryBits.sinkIndex, a.dimension_eq, ModularFamily.power,
    Nat.add_assoc]
  modulus_eq := a.modulus_eq
  exponent_eq := fun c => by simp [a.exponent_eq, ModularFamily.power, Nat.add_assoc]
  row_eq := fun _ => rfl
  col_eq := fun c => by simp [EntryBits.sinkIndex, a.dimension_eq, ModularFamily.power]
  entry_eq := fun c i j => by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact EntryBits.entry_correct a.bits c (F.modulus c) (F.dimension c) (F.row c) (F.column c) (F.matrix c)
      (a.dimension_eq c) (a.row_eq c) (a.column_eq c) (a.entry_eq c) i j

theorem power_controls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.power.ControlsPolyTime := by
  have hd := EntryBits.dimension_mem_FP_of_dimension a.bits ha.dimension
  have he := mem_FP_comp (mem_FP_comp ha.exponent Encoding.BinaryNat.succ_mem_FP) Encoding.BinaryNat.succ_mem_FP
  have hc := EntryBits.sinkIndex_mem_FP_of_dimension a.bits ha.dimension
  exact ⟨hd, ha.modulus, he, constFn_mem_FP [], hc⟩

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (R : SpaceFunction a.bits.row) (C : SpaceFunction a.bits.column) (A : SpaceFunction a.bits.entry) :
    SpaceFunction F.value := by
  have E := EntryBits.entryEvaluator a.bits ha.dimension R C A
  have P := MatrixPower.ModularAccess.evaluatorWithEntry a.power (power_controls a ha) E
  refine P.congr ?_
  funext c
  change residueBits ((matrixFin (F.row c) (F.column c) (F.matrix c) ^ (F.exponent c + 2)) 0
    (Fin.last (F.dimension c + 1))) = _
  rw [matrixFin_pow_moment]
  rfl

end ModularAccess
end LeanCanny.Algebra.MatrixMoment
