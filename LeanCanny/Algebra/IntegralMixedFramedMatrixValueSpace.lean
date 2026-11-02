/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedClearedPowerSum
public import LeanCanny.Algebra.ModularResidueSpace
/-! # Composing integer matrices on the same native old-bank rank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedMatrixValueBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedClearedMatrixBits (rank wrap)
open IntegralMixedFramedClearedPowerSumBits (row col)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
abbrev Matrices := (key : List Bool) → Matrix (Fin (rank P D H key)) (Fin (rank P D H key)) ℤ

noncomputable def matrixEntry (M : Matrices P D H) (key : List Bool) (r t : ℕ) :=
  M key (wrap P D H key r) (wrap P D H key t)
noncomputable def value (M : Matrices P D H) (q : List Bool) := residueBits
  (matrixEntry P D H M (PaddedIntegralGeneratorSource.base q)
    (Nat.fromBitsLE (PaddedIntegralGeneratorSource.row q)) (Nat.fromBitsLE (PaddedIntegralGeneratorSource.col q)) :
      ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))

theorem value_packet (M : Matrices P D H) (key mw : List Bool) (r t : Fin (rank P D H key)) :
    value P D H M (pair (pair key mw) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
      residueBits (M key r t : ZMod (Nat.fromBitsLE mw+1)) := by
  let p:=pair (pair key mw) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))
  have HE : matrixEntry P D H M (PaddedIntegralGeneratorSource.base p)
      (Nat.fromBitsLE (PaddedIntegralGeneratorSource.row p)) (Nat.fromBitsLE (PaddedIntegralGeneratorSource.col p))=M key r t := by
    simp only [p,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    rw [matrixEntry,show wrap P D H key r.val=r from Fin.ext (Nat.mod_eq_of_lt r.isLt),
      show wrap P D H key t.val=t from Fin.ext (Nat.mod_eq_of_lt t.isLt)]
  have HM : IntegralMixedFramedCompanionQueryBits.callerModulus p=Nat.fromBitsLE mw+1 := by
    simp only [p,IntegralMixedFramedCompanionQueryBits.callerModulus,PaddedIntegralGeneratorSource.modulus,pairFst_pair,pairSnd_pair]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ)=>residueBits (z : ZMod m)) HE HM

theorem sub_evaluator {M T : Matrices P D H} (EM : SpaceFunction (value P D H M)) (ET : SpaceFunction (value P D H T)) :
    SpaceFunction (value P D H (fun key=>M key-T key)) := by
  have EN := ModularResidueSpace.negEvaluator PaddedIntegralGeneratorSource.modulus _ PaddedIntegralGeneratorSource.modulus_FP ET
  have EE := ModularResidueSpace.addEvaluator PaddedIntegralGeneratorSource.modulus _ _ PaddedIntegralGeneratorSource.modulus_FP EM EN
  exact EE.congr (funext fun q=>by
    simp only [value,matrixEntry,Matrix.sub_apply,sub_eq_add_neg,Int.cast_add,Int.cast_neg])

theorem smul_evaluator {M : Matrices P D H} {f : List Bool → ℤ}
    (EF : SpaceFunction (fun q=>residueBits (f (PaddedIntegralGeneratorSource.base q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))))
    (EM : SpaceFunction (value P D H M)) : SpaceFunction (value P D H (fun key=>f key • M key)) := by
  have EE := ModularResidueSpace.mulEvaluator PaddedIntegralGeneratorSource.modulus _ _ PaddedIntegralGeneratorSource.modulus_FP EF EM
  exact EE.congr (funext fun q=>by simp only [value,matrixEntry,Matrix.smul_apply,zsmul_eq_mul,Int.cast_mul,Int.cast_id])

theorem diagonal_evaluator (a : Access P) {f : List Bool → ℤ}
    (EF : SpaceFunction (fun q=>residueBits (f (PaddedIntegralGeneratorSource.base q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q)))) :
    SpaceFunction (value P D H (fun key=>(f key : Matrix _ _ ℤ))) := by
  have HZ : SpaceFunction (fun q : List Bool=>residueBits (0 : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))) :=
    (SpaceFunction.ofFP (fun _=>[]) (constFn_mem_FP [])).congr (funext fun q=>ArithmeticBits.zero_residueBits _)
  have HP := (IntegralMixedFramedClearedPowerSumBits.row_binary P a D H).eq
    (IntegralMixedFramedClearedPowerSumBits.col_binary P a D H)
  have EE := ModularResidueSpace.branchEvaluator PaddedIntegralGeneratorSource.modulus _ _ _ HP EF HZ
  exact EE.congr (funext fun q=>by
    by_cases h : (row P D H q).val=(col P D H q).val
    · rw [ite_eq_left h]
      have HH : row P D H q=col P D H q := Fin.ext h
      change residueBits (f (PaddedIntegralGeneratorSource.base q) : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))=
        residueBits (((f (PaddedIntegralGeneratorSource.base q) : Matrix (Fin (rank P D H (PaddedIntegralGeneratorSource.base q)))
          (Fin (rank P D H (PaddedIntegralGeneratorSource.base q))) ℤ) (row P D H q) (col P D H q) : ℤ) :
          ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))
      rw [Matrix.intCast_apply,ite_eq_left HH,Int.cast_id]
    · rw [ite_eq_right h]
      have HH : ¬row P D H q=col P D H q := fun he=>h (congrArg Fin.val he)
      change residueBits (0 : ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))=
        residueBits (((f (PaddedIntegralGeneratorSource.base q) : Matrix (Fin (rank P D H (PaddedIntegralGeneratorSource.base q)))
          (Fin (rank P D H (PaddedIntegralGeneratorSource.base q))) ℤ) (row P D H q) (col P D H q) : ℤ) :
          ZMod (IntegralMixedFramedCompanionQueryBits.callerModulus q))
      simp only [Matrix.intCast_apply,HH,ite_false,Int.cast_zero])


end LeanCanny.Algebra.IntegralMixedFramedMatrixValueBits
