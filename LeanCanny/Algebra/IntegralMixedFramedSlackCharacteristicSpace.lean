/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrixSpace
public import LeanCanny.Algebra.IntegralScaledCharacteristicSpace
/-! # Native characteristic coefficients for the actual marked-slack matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (rank)
open IntegralMixedFramedMatrixValueBits (Matrices)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def characteristic (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) : IntegralBerkowitzBlockBits.Source where
  dimension z := rank P D H (RationalSubstitution.IntegerBits.context z)
  rank _ := 1
  carrier _ := ℤ
  ring _ := inferInstance
  nontrivial _ := inferInstance
  basis _ := Module.Basis.singleton (Fin 1) ℤ
  matrix z := M (RationalSubstitution.IntegerBits.context z)
  modulus := RationalSubstitution.IntegerBits.mValue
  modulus_ne_zero _ := by unfold RationalSubstitution.IntegerBits.mValue; omega
  coefficient z := Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree z)
  basisRow _ := 0
  basisCol _ := 0

def entryPacket (p : List Bool) :=
  let z:=IntegralBerkowitzBlockBits.original p
  pair (pair (RationalSubstitution.IntegerBits.context z) (pairSnd z))
    (pair (MatrixMoment.EntryBits.rowIndex p) (MatrixMoment.EntryBits.colIndex p))

theorem entryPacket_FP : entryPacket∈FP :=
  mem_FP_pair (mem_FP_pair
    (mem_FP_comp (f := IntegralBerkowitzBlockBits.original) (g := RationalSubstitution.IntegerBits.context) IntegralBerkowitzBlockBits.original_FP RationalSubstitution.IntegerBits.context_mem_FP)
    (mem_FP_comp (f := IntegralBerkowitzBlockBits.original) (g := pairSnd) IntegralBerkowitzBlockBits.original_FP pairSnd_mem_FP))
    (mem_FP_pair MatrixMoment.EntryBits.rowIndex_mem_FP MatrixMoment.EntryBits.colIndex_mem_FP)

private theorem singleton_entry (z : ℤ) (r t : Fin 1) : Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ) z r t=z := by
  rw [Algebra.leftMulMatrix_eq_repr_mul,Module.Basis.singleton_apply,mul_one,Module.Basis.singleton_repr]

noncomputable def access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) : IntegralBerkowitzBlockBits.Access (characteristic P D H M) where
  dimension := (IntegralMixedFramedClearedMatrixBits.rank_binary P a D H).comp RationalSubstitution.IntegerBits.context_mem_FP
  rank := BinaryFn.const 1
  modulus := (BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)
  coefficient := BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  basisRow := BinaryFn.const 0
  basisCol := BinaryFn.const 0
  entry := IntegralMixedFramedMatrixValueBits.value P D H M ∘ entryPacket
  entry_eq q i j r t := by
    let p:=pair (IntegralBlockMomentBits.context q r.val t.val)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
    have HP : entryPacket p=pair (pair (RationalSubstitution.IntegerBits.context q) (pairSnd q))
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
      simp only [p,entryPacket,IntegralBerkowitzBlockBits.original,IntegralBlockMomentBits.context,
        MatrixMoment.EntryBits.rowIndex,MatrixMoment.EntryBits.colIndex,pairFst_pair,pairSnd_pair]
    change IntegralMixedFramedMatrixValueBits.value P D H M (entryPacket p)=_
    rw [HP]
    change IntegralMixedFramedMatrixValueBits.value P D H M
      (pair (pair (RationalSubstitution.IntegerBits.context q) (pairSnd q))
        (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=
      residueBits (Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ)
        (M (RationalSubstitution.IntegerBits.context q) i j) r t : ZMod _)
    rw [singleton_entry]
    exact IntegralMixedFramedMatrixValueBits.value_packet P D H M (RationalSubstitution.IntegerBits.context q) (pairSnd q) i j

def scalarPacket (z : List Bool) := pair (pair (RationalSubstitution.IntegerBits.context z) (pairSnd z)) []
theorem scalarPacket_FP : scalarPacket∈FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP) (constFn_mem_FP [])

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) (scalar : List Bool → ℤ) (key : List Bool) :=
  ScaledGradedReductionAnnihilator.polynomial (M key) (scalar key) 1

theorem scaled_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (M : Matrices P D H) (scalar : List Bool → ℤ) (z : List Bool) :
    IntegralScaledCharacteristicBits.value (characteristic P D H M) (scalar ∘ RationalSubstitution.IntegerBits.context) (fun _=>1) z=
      PrimitivePairBits.coefficient (polynomial P D H M scalar) z := by
  unfold IntegralScaledCharacteristicBits.value
  change residueBits (Algebra.leftMulMatrix (Module.Basis.singleton (Fin 1) ℤ)
    ((polynomial P D H M scalar (RationalSubstitution.IntegerBits.context z)).coeff
      (Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree z))) 0 0 : ZMod _)=_
  rw [singleton_entry]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedSlackCharacteristicBits
