/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantPackingLayout
/-! # Native packets packing the actual formal homogeneous row coefficients

A source packet is `pair (pair context modulus) (pair row (pair spatialRank
parameterRank))`. The original context and selected coordinate stay fixed.
The parameter rank has blocks epsilon, target, radius, then center.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterQuery
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FixedWidthQuery.read

def context (q : List Bool) := pairFst (pairFst q)
def modulus (q : List Bool) := pairSnd (pairFst q)
def rowWord (q : List Bool) := pairFst (pairSnd q)
def spatialWord (q : List Bool) := pairFst (pairSnd (pairSnd q))
def parameterWord (q : List Bool) := pairSnd (pairSnd (pairSnd q))
theorem context_FP : context ∈ FP := by polytime [context]
theorem modulus_FP : modulus ∈ FP := by polytime [modulus]
theorem rowWord_FP : rowWord ∈ FP := by polytime [rowWord]
theorem spatialWord_FP : spatialWord ∈ FP := by polytime [spatialWord]
theorem parameterWord_FP : parameterWord ∈ FP := by polytime [parameterWord]

noncomputable def spatial (q : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.spatial (context q)
noncomputable def centers (q : List Bool) := d (pairFst (context q))
noncomputable def macroWidth (q : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.width (context q)
noncomputable def parameterWidth (q : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (context q)
noncomputable def sourceWidth (q : List Bool) := max (macroWidth q) (parameterWidth q)
noncomputable def sourceDimension (q : List Bool) := spatial q + centers q + 1
noncomputable def parameterDimension (q : List Bool) := centers q + 3

theorem spatial_unary : UnaryFn spatial := FormulaSignSlotRadialEliminantPackingLayout.spatial_unary.comp context_FP
theorem centers_unary : UnaryFn centers := FormulaSignSlotSource.dimension_unary.comp (mem_FP_comp context_FP pairFst_mem_FP)
theorem macroWidth_unary : UnaryFn macroWidth := FormulaSignSlotRadialEliminantPackingLayout.width_unary.comp context_FP
theorem parameterWidth_unary : UnaryFn parameterWidth := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp context_FP
theorem sourceWidth_unary : UnaryFn sourceWidth := macroWidth_unary.max parameterWidth_unary
theorem sourceDimension_unary : UnaryFn sourceDimension := (spatial_unary.add centers_unary).add (UnaryFn.const 1)
theorem parameterDimension_unary : UnaryFn parameterDimension := centers_unary.add (UnaryFn.const 3)

noncomputable def sourceEntry (q : List Bool) (i : ℕ) : ℕ :=
  if i < spatial q then
    FixedWidthQuery.entry (fun q => spatial q + 1) macroWidth spatialWord q (i + 1)
  else if i < spatial q + centers q then
    FixedWidthQuery.entry parameterDimension parameterWidth parameterWord q (i - spatial q + 3)
  else if i = spatial q + centers q then
    FixedWidthQuery.entry parameterDimension parameterWidth parameterWord q 2 else 0

noncomputable def sourceEntryReader (z : List Bool) : List Bool :=
  let q := pairFst z
  let i := Nat.fromBitsLE (pairSnd z)
  if i < spatial q then
    FixedWidthQuery.read (fun q => spatial q + 1) macroWidth spatialWord
      (pair q (BinaryNatCode.encode (i + 1)))
  else if i < spatial q + centers q then
    FixedWidthQuery.read parameterDimension parameterWidth parameterWord
      (pair q (BinaryNatCode.encode (i - spatial q + 3)))
  else if i = spatial q + centers q then
    FixedWidthQuery.read parameterDimension parameterWidth parameterWord (pair q (BinaryNatCode.encode 2)) else []

theorem sourceEntryReader_FP : sourceEntryReader ∈ FP := by
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  have HS := BinaryFn.ofUnary (spatial_unary.comp pairFst_mem_FP)
  have HC := BinaryFn.ofUnary (centers_unary.comp pairFst_mem_FP)
  have HSum := HS.add HC
  have HM := FixedWidthQuery.read_mem_FP (spatial_unary.add (UnaryFn.const 1)) macroWidth_unary spatialWord_FP
  have HP := FixedWidthQuery.read_mem_FP parameterDimension_unary parameterWidth_unary parameterWord_FP
  have HMQ := mem_FP_pair pairFst_mem_FP (HI.add (BinaryFn.const 1)).bits_mem_FP
  have HPQ := mem_FP_pair pairFst_mem_FP ((HI.sub HS).add (BinaryFn.const 3)).bits_mem_FP
  have HRQ := mem_FP_pair pairFst_mem_FP (constFn_mem_FP (BinaryNatCode.encode 2))
  have E := (HI.lt HS).ite_mem_FP (mem_FP_comp HMQ HM)
    ((HI.lt HSum).ite_mem_FP (mem_FP_comp HPQ HP)
      ((HI.eq HSum).ite_mem_FP (mem_FP_comp HRQ HP) (constFn_mem_FP [])))
  exact mem_FP_of_eq E (fun _ => rfl)

theorem sourceEntryReader_packet (q : List Bool) (i : ℕ) :
    sourceEntryReader (pair q (BinaryNatCode.encode i)) = BinaryNatCode.encode (sourceEntry q i) := by
  simp only [sourceEntryReader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  unfold sourceEntry
  split_ifs <;> first | exact FixedWidthQuery.read_packet _ _ _ _ _ | rfl

noncomputable def sourceWord (q : List Bool) : List Bool :=
  FixedWidthNatVector.encode (sourceDimension q) (sourceWidth q) (sourceEntry q)
theorem sourceWord_FP : sourceWord ∈ FP :=
  FixedWidthNatVector.encode_mem_FP _ _ _ sourceDimension_unary sourceWidth_unary _
    sourceEntryReader_FP sourceEntryReader_packet

noncomputable def packet (q : List Bool) : List Bool :=
  pair (pairFst (context q)) (WordList.encode [FormulaSignSlotRadialEliminantInput.field 0 (context q),
    rowWord q, List.replicate (sourceWidth q) true, sourceWord q,
    (spatialWord q).take (macroWidth q), (parameterWord q).take (parameterWidth q),
    ((parameterWord q).drop (parameterWidth q)).take (parameterWidth q), modulus q])

theorem packet_FP : packet ∈ FP := by
  have HO := mem_FP_comp context_FP pairFst_mem_FP
  have HI := mem_FP_comp context_FP (FormulaSignSlotRadialEliminantInput.field_FP 0)
  have HH := take_mem_FP spatialWord_FP macroWidth_unary
  have HE := take_mem_FP parameterWord_FP parameterWidth_unary
  have HT := take_mem_FP (drop_mem_FP parameterWord_FP parameterWidth_unary) parameterWidth_unary
  have H := mem_FP_pair HO (mem_FP_pair HI (mem_FP_pair rowWord_FP
    (mem_FP_pair (sourceWidth_unary.replicate_mem_FP true) (mem_FP_pair sourceWord_FP
      (mem_FP_pair HH (mem_FP_pair HE (mem_FP_pair HT (mem_FP_pair modulus_FP (constFn_mem_FP [])))))))))
  exact mem_FP_of_eq H (fun _ => rfl)

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterQuery
