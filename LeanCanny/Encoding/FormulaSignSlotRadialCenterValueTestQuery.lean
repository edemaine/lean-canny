/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValuePacking
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantSource
public import LeanCanny.Algebra.FixedWidthBlockRenameSpace
/-! # A full original-term coefficient query from spatial and joint parameter words -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTestQuery
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open MacaulayFullBoxBits (ctx shift uv ctx_FP shift_FP uv_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def base := AffineValueGramBits.base
def original (z : List Bool) := FormulaSignSlotRadialCenterValueLayout.original (base z)
def parameter (z : List Bool) := pairFst (uv z)
def modulus (z : List Bool) := pairSnd (ctx z)
noncomputable def spatialCount (z : List Bool) := FormulaSignSlotRadialCenterValueLayout.arity (base z)
noncomputable def centers (z : List Bool) := d (original z)
noncomputable def parameterCount (z : List Bool) := FormulaSignSlotRadialCenterValuePacking.arity (base z)
noncomputable def spatialWidth (z : List Bool) := FormulaSignSlotRadialCenterValueLayout.width (base z)
noncomputable def parameterWidth (z : List Bool) := FormulaSignSlotRadialCenterValuePacking.width (base z)
noncomputable def fullCount (z : List Bool) := FormulaSignSlotRadialFormalInput.dimension (original z)
noncomputable def width (z : List Bool) := spatialWidth z + parameterWidth z
noncomputable def spatialEntry := FixedWidthQuery.entry spatialCount spatialWidth shift
noncomputable def parameterEntry := FixedWidthQuery.entry parameterCount parameterWidth parameter
noncomputable def entry (z : List Bool) (i : ℕ) := if i < spatialCount z then spatialEntry z i
  else if i < spatialCount z + centers z then parameterEntry z (i - spatialCount z + 1) else parameterEntry z 0
noncomputable def word (z : List Bool) := FixedWidthNatVector.encode (fullCount z) (width z) (entry z)

theorem base_FP : base ∈ FP := AffineValueGramBits.base_FP
theorem original_FP : original ∈ FP := mem_FP_comp base_FP FormulaSignSlotRadialCenterValueLayout.original_FP
theorem parameter_FP : parameter ∈ FP := mem_FP_comp uv_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp ctx_FP pairSnd_mem_FP
theorem spatialCount_unary : UnaryFn spatialCount := FormulaSignSlotRadialCenterValueLayout.arity_unary.comp base_FP
theorem centers_unary : UnaryFn centers := FormulaSignSlotSource.dimension_unary.comp original_FP
theorem parameterCount_unary : UnaryFn parameterCount := FormulaSignSlotRadialCenterValuePacking.arity_unary.comp base_FP
theorem spatialWidth_unary : UnaryFn spatialWidth := FormulaSignSlotRadialCenterValueLayout.width_unary.comp base_FP
theorem parameterWidth_unary : UnaryFn parameterWidth := FormulaSignSlotRadialCenterValuePacking.width_unary.comp base_FP
theorem fullCount_unary : UnaryFn fullCount := FormulaSignSlotRadialFormalInput.dimension_unary.comp original_FP
theorem width_unary : UnaryFn width := spatialWidth_unary.add parameterWidth_unary

noncomputable def parameterQuery (q : List Bool) := pair (pairFst q)
  (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) - spatialCount (pairFst q) + 1))
theorem parameterQuery_FP : parameterQuery ∈ FP := by
  have HI : BinaryFn (fun q => Nat.fromBitsLE (pairSnd q)) := BinaryFn.fromBits pairSnd_mem_FP
  have HM : BinaryFn (fun q => spatialCount (pairFst q)) := BinaryFn.ofUnary (spatialCount_unary.comp pairFst_mem_FP)
  exact mem_FP_pair pairFst_mem_FP ((HI.sub HM).add (BinaryFn.const 1)).bits_mem_FP
def radiusQuery (q : List Bool) := pair (pairFst q) (BinaryNatCode.encode 0)
theorem radiusQuery_FP : radiusQuery ∈ FP := mem_FP_pair pairFst_mem_FP (constFn_mem_FP _)

noncomputable def entryReader (q : List Bool) :=
  if Nat.fromBitsLE (pairSnd q) < spatialCount (pairFst q) then FixedWidthQuery.read spatialCount spatialWidth shift q
  else if Nat.fromBitsLE (pairSnd q) < spatialCount (pairFst q) + centers (pairFst q) then
    FixedWidthQuery.read parameterCount parameterWidth parameter (parameterQuery q)
  else FixedWidthQuery.read parameterCount parameterWidth parameter (radiusQuery q)
theorem entryReader_FP : entryReader ∈ FP := by
  have HI : BinaryFn (fun q => Nat.fromBitsLE (pairSnd q)) := BinaryFn.fromBits pairSnd_mem_FP
  have HM := BinaryFn.ofUnary (spatialCount_unary.comp pairFst_mem_FP)
  have HMC := BinaryFn.ofUnary ((spatialCount_unary.add centers_unary).comp pairFst_mem_FP)
  have ES := FixedWidthQuery.read_mem_FP spatialCount_unary spatialWidth_unary shift_FP
  have EP := FixedWidthQuery.read_mem_FP parameterCount_unary parameterWidth_unary parameter_FP
  exact (HI.lt HM).ite_mem_FP ES ((HI.lt HMC).ite_mem_FP
    (mem_FP_comp parameterQuery_FP EP) (mem_FP_comp radiusQuery_FP EP))

attribute [local irreducible] spatialCount centers parameterCount spatialWidth parameterWidth fullCount width
  spatialEntry parameterEntry

theorem entryReader_packet (z : List Bool) (i : ℕ) :
    entryReader (pair z (BinaryNatCode.encode i)) = BinaryNatCode.encode (entry z i) := by
  unfold entryReader
  simp only [pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
  split_ifs with HS HC
  · rw [FixedWidthQuery.read_packet]
    rw [entry, ite_eq_left HS, spatialEntry]
  · simp only [parameterQuery, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode]
    rw [FixedWidthQuery.read_packet, entry, ite_eq_right HS, ite_eq_left HC, parameterEntry]
  · simp only [radiusQuery, pairFst_pair]
    rw [FixedWidthQuery.read_packet, entry, ite_eq_right HS, ite_eq_right HC, parameterEntry]

theorem word_FP : word ∈ FP := FixedWidthNatVector.encode_mem_FP fullCount width entry
  fullCount_unary width_unary entryReader entryReader_FP entryReader_packet

theorem entry_fit (z : List Bool) (i : ℕ) : entry z i < 2 ^ width z := by
  have HS : spatialEntry z i < 2 ^ spatialWidth z := by
    unfold spatialEntry FixedWidthQuery.entry FixedWidthQuery.coordinate
    split_ifs
    · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
        (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
    · exact Nat.two_pow_pos _
  have HP (j : ℕ) : parameterEntry z j < 2 ^ parameterWidth z := by
    unfold parameterEntry FixedWidthQuery.entry FixedWidthQuery.coordinate
    split_ifs
    · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
        (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
    · exact Nat.two_pow_pos _
  unfold entry width
  split_ifs
  · exact HS.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · exact (HP _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  · exact (HP _).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

noncomputable def exponent (z : List Bool) := nativeExponent (Equiv.refl (Fin (fullCount z)))
  (width z) (Nat.fromBitsLE (word z))
theorem exponent_entry (z : List Bool) (i : Fin (fullCount z)) : exponent z i = entry z i.val := by
  simp only [exponent, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, Equiv.refl_apply,
    FixedWidthBlockRenameBits.entry_bits]
  exact FixedWidthNatVector.decode_block _ _ _ i.val i.isLt (entry_fit z i.val)

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTestQuery
