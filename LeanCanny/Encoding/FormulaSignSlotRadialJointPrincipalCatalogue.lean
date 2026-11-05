/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalBounds
public import LeanCanny.Encoding.ChargedPolynomialCatalogue
/-! # Every bounded principal coefficient on the actual joint center -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation
open FormulaSignSlotRadialJointCoefficientCatalogue (degree limit)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "S" => FormulaSignSlotRadialJointPrincipalSource.source

noncomputable def radiusLimit (c : List Bool) := FormulaSignSlotRadialJointPrincipalBounds.degreeBound c+1
noncomputable def count (c : List Bool) := FormulaSignSlotRadialJointLayout.spatialCount c*(limit c*(limit c*(limit c*radiusLimit c)))
noncomputable def radiusIndex (c : List Bool) (i : ℕ) := i%radiusLimit c
noncomputable def orderIndex (c : List Bool) (i : ℕ) := (i/radiusLimit c)%limit c
noncomputable def declaredIndex (c : List Bool) (i : ℕ) := (i/radiusLimit c/limit c)%limit c
noncomputable def tauIndex (c : List Bool) (i : ℕ) := (i/radiusLimit c/limit c/limit c)%limit c
noncomputable def coordinate (c : List Bool) (i : ℕ) := i/radiusLimit c/limit c/limit c/limit c
noncomputable def row (q : List Bool) := pair (pairFst q) (WordList.encode
  [BinaryNatCode.encode (coordinate (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (tauIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (declaredIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (orderIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))),
   BinaryNatCode.encode (radiusIndex (pairFst q) (Nat.fromBitsLE (pairSnd q)))])
noncomputable def familyContext (c : List Bool) (i : ℕ) := pairFst
  (FormulaSignSlotRadialJointPrincipalSource.read (row (pair c (BinaryNatCode.encode i))))

theorem root_eq (c : List Bool) (i : ℕ) :
    pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (familyContext c i))=
      FormulaSignSlotRadialJointLayout.source true c := by
  have H := FormulaSignSlotRadialJointPrincipalSource.radial_root (row (pair c (BinaryNatCode.encode i)))
  simpa only [familyContext,FormulaSignSlotRadialJointPrincipalSource.radial,
    FormulaSignSlotRadialJointPrincipalSource.header,row,pairFst_pair] using H

theorem declared_eq (c : List Bool) (i : ℕ) :
    FormulaSignSlotRadialCenterPrincipalFamily.degree (familyContext c i)=declaredIndex c i := by
  simp only [familyContext,FormulaSignSlotRadialJointPrincipalSource.read,
    FormulaSignSlotRadialCenterPrincipalFamily.degree,FormulaSignSlotRadialJointPrincipalSource.slot,
    row,WordList.reader,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

theorem declared_le (c : List Bool) (i : ℕ) :
    FormulaSignSlotRadialCenterPrincipalFamily.degree (familyContext c i) ≤ degree c := by
  rw [declared_eq]
  unfold declaredIndex
  have H := Nat.mod_lt (i/radiusLimit c/limit c) (Nat.zero_lt_succ (degree c))
  exact Nat.le_of_lt_succ H

theorem arity_eq (c : List Bool) (i : ℕ) :
    (S).arity (row (pair c (BinaryNatCode.encode i)))=FormulaSignSlotRadialJointLayout.dimension c := by
  change FormulaSignSlotRadialJointLayout.dimension
    (FormulaSignSlotRadialJointPrincipalSource.header (row (pair c (BinaryNatCode.encode i))))=_
  simp only [FormulaSignSlotRadialJointPrincipalSource.header,row,pairFst_pair]
theorem degree_le (c : List Bool) (i : ℕ) :
    (S).degree (row (pair c (BinaryNatCode.encode i))) ≤ FormulaSignSlotRadialJointPrincipalBounds.degreeBound c :=
  FormulaSignSlotRadialJointPrincipalBounds.degree_le c (familyContext c i) (root_eq c i) (declared_le c i)
theorem mass_le (c : List Bool) (i : ℕ) :
    (S).mass (row (pair c (BinaryNatCode.encode i))) ≤ FormulaSignSlotRadialJointPrincipalBounds.massBound c :=
  FormulaSignSlotRadialJointPrincipalBounds.mass_le c (familyContext c i) (root_eq c i) (declared_le c i)

noncomputable def input : ChargedPolynomialCatalogue.Input where
  source := S
  row := row
  arity := FormulaSignSlotRadialJointLayout.dimension
  count := count
  degree := FormulaSignSlotRadialJointPrincipalBounds.degreeBound
  mass := FormulaSignSlotRadialJointPrincipalBounds.massBound
  dimension := arity_eq
  degree_bound := degree_le
  mass_bound := mass_le
noncomputable def family := ChargedPolynomialCatalogue.family input

theorem radiusLimit_binary : BinaryFn radiusLimit :=
  FormulaSignSlotRadialJointPrincipalBounds.degreeBound_binary.add (BinaryFn.const 1)
theorem count_binary : BinaryFn count :=
  (BinaryFn.ofUnary FormulaSignSlotRadialJointLayout.spatialCount_unary).mul
    (FormulaSignSlotRadialJointCoefficientCatalogue.limit_binary.mul
      (FormulaSignSlotRadialJointCoefficientCatalogue.limit_binary.mul
        (FormulaSignSlotRadialJointCoefficientCatalogue.limit_binary.mul radiusLimit_binary)))
theorem row_FP : row ∈ FP := by
  have HI : BinaryFn (fun q => Nat.fromBitsLE (pairSnd q)) := BinaryFn.fromBits pairSnd_mem_FP
  have HL : BinaryFn (fun q => limit (pairFst q)) := FormulaSignSlotRadialJointCoefficientCatalogue.limit_binary.comp pairFst_mem_FP
  have HB : BinaryFn (fun q => radiusLimit (pairFst q)) := radiusLimit_binary.comp pairFst_mem_FP
  have HR : BinaryFn (fun q => radiusIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := HI.mod HB
  have HO : BinaryFn (fun q => orderIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := (HI.div HB).mod HL
  have HD : BinaryFn (fun q => declaredIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := ((HI.div HB).div HL).mod HL
  have HS : BinaryFn (fun q => tauIndex (pairFst q) (Nat.fromBitsLE (pairSnd q))) := (((HI.div HB).div HL).div HL).mod HL
  have HC : BinaryFn (fun q => coordinate (pairFst q) (Nat.fromBitsLE (pairSnd q))) := (((HI.div HB).div HL).div HL).div HL
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair HC.bits_mem_FP (mem_FP_pair HS.bits_mem_FP
    (mem_FP_pair HD.bits_mem_FP (mem_FP_pair HO.bits_mem_FP (mem_FP_pair HR.bits_mem_FP (constFn_mem_FP []))))))

theorem source_fit (z : List Bool) : (S).degree z < 2^(S).width z := by
  dsimp only [FormulaSignSlotRadialJointPrincipalSource.source,IntegralFramedBankPolynomialEmbedding.source]
  exact FormulaSignSlotRadialJointPrincipalSource.degree_fit z
noncomputable def input_access : ChargedPolynomialCatalogue.Access input where
  source := FormulaSignSlotRadialJointPrincipalSource.access
  row := row_FP
  arity := FormulaSignSlotRadialJointLayout.dimension_unary
  count := count_binary
  degree := FormulaSignSlotRadialJointPrincipalBounds.degreeBound_binary
  mass := FormulaSignSlotRadialJointPrincipalBounds.massBound_binary
  fit := source_fit
noncomputable def access : SquareFeatureProductFamily.Access family := ChargedPolynomialCatalogue.access input input_access

end LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalCatalogue
