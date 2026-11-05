/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialCoordinatePacket
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSliceEvaluation
/-! # Literal joint columns for actual grid-anchor equations

The datum is pair joint-header (pair coordinate perturbation). Target,
radius, and center columns are the ones already present in the joint core.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGridLayout
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def header (z : List Bool) := pairFst z
def coordinateWord (z : List Bool) := pairFst (pairSnd z)
def tauInput (z : List Bool) := pairSnd (pairSnd z)
noncomputable def sliceContext (z : List Bool) := pair
  (FormulaSignSlotRadialCoordinatePacket.writer
    (pair (FormulaSignSlotRadialJointLayout.source true (header z)) (coordinateWord z))) (tauInput z)
noncomputable def radial (z : List Bool) := pairFst (sliceContext z)
noncomputable def tauWord (z : List Bool) := pairSnd (sliceContext z)
theorem header_FP : header ∈ FP := pairFst_mem_FP
theorem coordinateWord_FP : coordinateWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem tauInput_FP : tauInput ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
theorem sliceContext_FP : sliceContext ∈ FP := by
  have HS : (fun z => FormulaSignSlotRadialJointLayout.source true (header z)) ∈ FP :=
    mem_FP_comp (f := header) (g := FormulaSignSlotRadialJointLayout.source true)
      header_FP (FormulaSignSlotRadialJointLayout.source_FP true)
  have HP : (fun z => pair (FormulaSignSlotRadialJointLayout.source true (header z)) (coordinateWord z)) ∈ FP :=
    mem_FP_pair HS coordinateWord_FP
  have HR : (fun z => FormulaSignSlotRadialCoordinatePacket.writer
      (pair (FormulaSignSlotRadialJointLayout.source true (header z)) (coordinateWord z))) ∈ FP :=
    mem_FP_comp (f := fun z => pair (FormulaSignSlotRadialJointLayout.source true (header z)) (coordinateWord z))
      (g := FormulaSignSlotRadialCoordinatePacket.writer) HP FormulaSignSlotRadialCoordinatePacket.writer_FP
  exact mem_FP_pair HR tauInput_FP
attribute [local irreducible] sliceContext
theorem radial_FP : radial ∈ FP := mem_FP_comp (f := sliceContext) (g := pairFst) sliceContext_FP pairFst_mem_FP
theorem tauWord_FP : tauWord ∈ FP := mem_FP_comp (f := sliceContext) (g := pairSnd) sliceContext_FP pairSnd_mem_FP
theorem radial_root (z : List Bool) : pairFst (radial z) = FormulaSignSlotRadialJointLayout.source true (header z) := by
  simp only [radial,sliceContext,FormulaSignSlotRadialCoordinatePacket.writer,pairFst_pair]

noncomputable def selected (z : List Bool) := (FormulaSignSlotRadialEliminantInput.coordinate (radial z)).val
theorem selected_unary : UnaryFn selected := FormulaSignSlotRadialEliminantInput.coordinate_unary.comp radial_FP
theorem selected_lt (z : List Bool) : selected z < FormulaSignSlotRadialJointLayout.spatialCount (header z) := by
  have H := (FormulaSignSlotRadialEliminantInput.coordinate (radial z)).isLt
  change selected z < FormulaSignSlotRadialFormalInput.spatial (pairFst (radial z)) at H
  rw [radial_root] at H
  exact H
theorem center_count (z : List Bool) : FormulaSignSlotCenteredRadialGraph.d (pairFst (radial z)) =
    FormulaSignSlotRadialJointLayout.centerCount (header z) := congrArg _ (radial_root z)

noncomputable def column (z : List Bool) (i : ℕ) : ℕ :=
  if i=0 then FormulaSignSlotRadialJointLayout.column 2 (selected z)
  else if i=1 then FormulaSignSlotRadialJointLayout.radiusVariable (header z)
  else FormulaSignSlotRadialJointLayout.column 0 (i-2)
theorem column_lt (z : List Bool)
    (i : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (radial z))+2)) :
    column z i.val < FormulaSignSlotRadialJointLayout.dimension (header z) := by
  unfold column
  split_ifs with H0 H1
  · exact FormulaSignSlotRadialJointLayout.column_lt _ _ _ (by decide)
      ((selected_lt z).trans_le ((by
        have HF := FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
        change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
          (FormulaSignSlotRadialJointLayout.centerCount (header z)+1) ≤ _ at HF
        omega)))
  · exact FormulaSignSlotRadialJointLayout.radiusVariable_lt _
  · apply FormulaSignSlotRadialJointLayout.column_lt _ _ _ (by decide)
    have HI := i.isLt
    have HC := center_count z
    have HF := FormulaSignSlotRadialJointLayout.formal_le_slots (header z)
    change FormulaSignSlotRadialJointLayout.spatialCount (header z)+
      (FormulaSignSlotRadialJointLayout.centerCount (header z)+1) ≤ _ at HF
    omega

noncomputable def embedding (z : List Bool) :
    Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (radial z))+2) →
      Fin (FormulaSignSlotRadialJointLayout.dimension (header z)) := fun i => ⟨column z i.val,column_lt z i⟩
theorem injective (z : List Bool) : Function.Injective (embedding z) := by
  intro i j H
  apply Fin.ext
  have HE := congrArg Fin.val H
  change column z i.val=column z j.val at HE
  have HS := selected_lt z
  unfold column FormulaSignSlotRadialJointLayout.radiusVariable FormulaSignSlotRadialJointLayout.column at HE
  split_ifs at HE <;> omega

noncomputable def dimension (z : List Bool) := FormulaSignSlotRadialJointLayout.dimension (header z)
theorem dimension_unary : UnaryFn dimension := FormulaSignSlotRadialJointLayout.dimension_unary.comp header_FP
noncomputable def columnCode (p : List Bool) := BinaryNatCode.encode (column (pairFst p) (Nat.fromBitsLE (pairSnd p)))
theorem columnCode_FP : columnCode ∈ FP := by
  have HI : BinaryFn (fun p => Nat.fromBitsLE (pairSnd p)) := BinaryFn.fromBits pairSnd_mem_FP
  have HS : BinaryFn (fun p => selected (pairFst p)) := BinaryFn.ofUnary (selected_unary.comp pairFst_mem_FP)
  have HR : BinaryFn (fun p => FormulaSignSlotRadialJointLayout.radiusVariable (header (pairFst p))) :=
    ((BinaryFn.const 4).mul (BinaryFn.ofUnary
      ((FormulaSignSlotRadialJointLayout.spatialCount_unary.add
        FormulaSignSlotRadialJointLayout.centerCount_unary).comp (mem_FP_comp pairFst_mem_FP header_FP)))).add (BinaryFn.const 2)
  have HC : BinaryFn (fun p => column (pairFst p) (Nat.fromBitsLE (pairSnd p))) :=
    BinaryFn.ite (HI.eq (BinaryFn.const 0)) ((BinaryFn.const 4).mul HS |>.add (BinaryFn.const 2))
      (BinaryFn.ite (HI.eq (BinaryFn.const 1)) HR ((BinaryFn.const 4).mul (HI.sub (BinaryFn.const 2))))
  exact HC.bits_mem_FP

theorem columnCode_packet (z : List Bool)
    (i : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst (radial z))+2)) :
    columnCode (pair z (BinaryNatCode.encode i.val)) = BinaryNatCode.encode (embedding z i).val := by
  simp only [columnCode,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,embedding]

noncomputable def polynomial (z : List Bool) := rename (embedding z)
  (FormulaSignSlotRadialGridSlice.polynomial (radial z) (Nat.fromBitsLE (tauWord z)))

end LeanCanny.Encoding.FormulaSignSlotRadialJointGridLayout
