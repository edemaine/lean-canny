/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightSpace
public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace
public import LeanCanny.Algebra.IntegralMixedFramedBankProducts
/-! # The actual old cleared-coordinate matrix as an integer characteristic source

A source context pairs the complete old saved key with a retained index.
Inactive native births and invalid retained labels have a literal zero matrix.
This total extension never replaces an active old matrix by a supplied reader.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def key (c : List Bool) := pairFst c
def index (c : List Bool) := Nat.fromBitsLE (pairSnd c)
def context (z : List Bool) := RationalSubstitution.IntegerBits.context z
noncomputable abbrev family (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) := IntegralMixedFramedHistoryFamilyBits.family P D H
noncomputable def count (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) := (family P D H).birth (key c)
noncomputable def dimension (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) := FixedWidthPolynomial.count (count P D H c) ((family P D H).width (key c))
def Active (P : Parameters) (c : List Bool) : Prop := IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)<P.cap (pairFst (key c))

noncomputable def matrix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) : Matrix (Fin (dimension P D H c)) (Fin (dimension P D H c)) ℤ :=
  fun r t => if Active P c then IntegralMixedFramedOldHeightBankBits.sourceEntry P D H (key c)
    (min (index c) (count P D H c)) r.val t.val else 0

noncomputable def common (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) : ℤ := IntegralMixedHistory.commonDenominator ((family P D H).state (key c))
noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) : Polynomial ℤ :=
  ScaledGradedReductionAnnihilator.polynomial (matrix P D H c) (common P D H c) 1

theorem count_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : List Bool) :
    count P D H c=IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c) := IntegralMixedFramedHistoryFamilyBits.family_birth P D H _

theorem count_unary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : UnaryFn (count P D H) :=
  ((IntegralMixedFullHistoryFamilyBits.prefix_unary P a).comp pairFst_mem_FP).of_eq (fun c => (count_eq P D H c).symm)

theorem dimension_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : BinaryFn (dimension P D H) :=
  ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))).powUnary (count_unary P a D H)

noncomputable def characteristic (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) : IntegralBerkowitzBlockBits.Source where
  dimension z := dimension P D H (context z)
  rank _ := 1
  carrier _ := ℤ
  ring _ := inferInstance
  nontrivial _ := inferInstance
  basis _ := Module.Basis.singleton (Fin 1) ℤ
  matrix z := matrix P D H (context z)
  modulus := RationalSubstitution.IntegerBits.mValue
  modulus_ne_zero _ := by unfold RationalSubstitution.IntegerBits.mValue; omega
  coefficient z := Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree z)
  basisRow _ := 0
  basisCol _ := 0

/-- The original coefficient query survives as the innermost context. -/
def entryPacket (p : List Bool) :=
  let z := IntegralBerkowitzBlockBits.original p
  let c := context z
  pair (pair (pair (key c) (pairSnd z))
    (pair (MatrixMoment.EntryBits.rowIndex p) (MatrixMoment.EntryBits.colIndex p))) (pairSnd c)

theorem entryPacket_FP : entryPacket∈FP := by
  have HC := mem_FP_comp IntegralBerkowitzBlockBits.original_FP RationalSubstitution.IntegerBits.context_mem_FP
  exact mem_FP_pair (mem_FP_pair (mem_FP_pair (mem_FP_comp HC pairFst_mem_FP)
    (mem_FP_comp IntegralBerkowitzBlockBits.original_FP pairSnd_mem_FP))
    (mem_FP_pair MatrixMoment.EntryBits.rowIndex_mem_FP MatrixMoment.EntryBits.colIndex_mem_FP)) (mem_FP_comp HC pairSnd_mem_FP)

noncomputable def entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedOldHeightQueryBits.value P D H ∘ entryPacket

private theorem singleton_entry (z : ℤ) (r t : Fin 1) : Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ) z r t=z := by
  rw [Algebra.leftMulMatrix_eq_repr_mul,Module.Basis.singleton_apply,mul_one,Module.Basis.singleton_repr]

attribute [local irreducible] IntegralMixedFramedOldHeightBankBits.sourceEntry matrix count dimension

private theorem entry_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c mw : List Bool) (i j : Fin (dimension P D H c)) :
    IntegralMixedFramedOldHeightQueryBits.value P D H
      (pair (pair (pair (key c) mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (pairSnd c))=
      residueBits (matrix P D H c i j : ZMod (Nat.fromBitsLE mw+1)) := by
  have HR : FixedWidthPolynomial.count (IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c))
      (P.width (pairFst (key c)))=dimension P D H c := by
    rw [dimension,count_eq]
    rfl
  let p := pair (pair (pair (key c) mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (pairSnd c)
  have HM : IntegralMixedFramedOldHeightQueryBits.callerModulus p=Nat.fromBitsLE mw+1 := by
    simp only [p,IntegralMixedFramedOldHeightQueryBits.callerModulus,IntegralMixedFramedOldHeightQueryBits.source,
      IntegralMixedFramedCompanionQueryBits.callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  change IntegralMixedFramedOldHeightQueryBits.value P D H p=_
  unfold IntegralMixedFramedOldHeightQueryBits.value
  rw [HM]
  simp only [p,IntegralMixedFramedOldHeightQueryBits.Active,
    IntegralMixedFramedOldHeightQueryBits.sourceBirth,IntegralMixedFramedOldHeightQueryBits.key,
    IntegralMixedFramedOldHeightQueryBits.root,IntegralMixedFramedOldHeightQueryBits.source,
    IntegralMixedFramedOldHeightQueryBits.retainedIndex,
    IntegralMixedFramedOldHeightQueryBits.rowIndex,IntegralMixedFramedOldHeightQueryBits.colIndex,
    IntegralMixedFramedOldHeightQueryBits.sourceRank,
    PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    HR,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt]
  by_cases ha : Active P c
  · have HA : IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)<P.cap (pairFst (key c)) := ha
    rw [ite_eq_left HA,matrix,ite_eq_left ha,count_eq]
    rfl
  · have HA : ¬IntegralMixedFramedHistoryFamilyBits.prefixLength P (key c)<P.cap (pairFst (key c)) := ha
    rw [ite_eq_right HA,matrix,ite_eq_right ha,Int.cast_zero]
    exact ArithmeticBits.zero_residueBits _

noncomputable def access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :
    IntegralBerkowitzBlockBits.Access (characteristic P D H) where
  dimension := (dimension_binary P a D H).comp RationalSubstitution.IntegerBits.context_mem_FP
  rank := BinaryFn.const 1
  modulus := (BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)
  coefficient := BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  basisRow := BinaryFn.const 0
  basisCol := BinaryFn.const 0
  entry := entry P D H
  entry_eq q i j r t := by
    let p := pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    have HO : IntegralBerkowitzBlockBits.original p=q := by simp only [p,IntegralBerkowitzBlockBits.original,IntegralBlockMomentBits.context,pairFst_pair]
    have HI : MatrixMoment.EntryBits.rowIndex p=BinaryNatCode.encode i.val := by simp only [p,MatrixMoment.EntryBits.rowIndex,pairFst_pair,pairSnd_pair]
    have HJ : MatrixMoment.EntryBits.colIndex p=BinaryNatCode.encode j.val := by simp only [p,MatrixMoment.EntryBits.colIndex,pairSnd_pair]
    change entry P D H p=_
    rw [entry,Function.comp_apply,entryPacket,HO,HI,HJ]
    change IntegralMixedFramedOldHeightQueryBits.value P D H
      (pair (pair (pair (key (context q)) (pairSnd q)) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) (pairSnd (context q)))=
      residueBits (Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ) (matrix P D H (context q) i j) r t : ZMod _)
    rw [singleton_entry]
    exact entry_packet P D H (context q) (pairSnd q) i j

theorem scaled_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralScaledCharacteristicBits.value (characteristic P D H) (fun z => common P D H (context z)) (fun _ => 1) q=
      PrimitivePairBits.coefficient (polynomial P D H) q := by
  unfold IntegralScaledCharacteristicBits.value
  change residueBits (Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ)
    ((polynomial P D H (context q)).coeff (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree q))) 0 0 : ZMod _)=_
  rw [singleton_entry]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicBits
