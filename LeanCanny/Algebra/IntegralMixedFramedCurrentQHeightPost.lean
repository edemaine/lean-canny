/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightCosts
/-! # Current-bank sweep slopes from charged earlier-producer replies

An original mode flag chooses literal slopes or current-Q times an original
multiplier. Q is read solely from the previously charged leading table.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
open IntegralMixedFramedHeightPostBits (guard guard_FP constantBranch constantBranch_FP slopeBranch slopeBranch_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.mulMod modulus IntegralMixedFramedScalarCellsBits.cell
  IntegralMixedFramedHeightIntegerBits.bank IntegralMixedFramedNativeHeightBits.model
  IntegralMixedFramedHeightTablePassBits.value

structure Controls (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  low : LowControls P D J
  current : List Bool → Bool
  current_FP : (fun q => [current q])∈FP
  multiplier : List Bool → ℤ
  multiplier_space : SpaceFunction (fun q => residueBits (multiplier q : ZMod (modulus P q)))
  slope : ∀ q,IntegralMixedFramedScalarCellsBits.cell P D J q 3 0=
    (if current q then IntegralMixedFramedHeightIntegerBits.bank P D J q else 1)*multiplier q

noncomputable def bankFactor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (z : List Bool) :=
  if h.current (pairFst z) then IntegralMixedFramedHeightBankProductBits.value P z
  else ArithmeticBits.one (BinaryNatCode.encode (modulus P (pairFst z)))

attribute [local irreducible] bankFactor

theorem bankFactor_FP (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : bankFactor P D J h∈FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  have HP : FPPred (fun z => h.current (pairFst z)=true) := (FPPred.of_flag h.current_FP).comp pairFst_mem_FP
  exact mem_FP_of_eq (HP.ite_mem_FP (IntegralMixedFramedHeightBankProductBits.value_FP P a)
    (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)) (fun z => by unfold bankFactor; rfl)

noncomputable def multiplierWord (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool) :=
  residueBits (h.multiplier q : ZMod (modulus P q))
attribute [local irreducible] multiplierWord

noncomputable def slopeCoefficient (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (z : List Bool) :=
  multiply P (pair z (pair (bankFactor P D J h z) (multiplierWord P D J h (pairFst z))))

attribute [local irreducible] slopeCoefficient

theorem slopeCoefficient_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : SpaceFunction (slopeCoefficient P D J h) := by
  have E := ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((SpaceFunction.ofFP _ (bankFactor_FP P a D J h)).pairOutputs
    (h.multiplier_space.precompose pairFst pairFst_mem_FP))).postcompose (multiply P) (multiply_FP P a)
  exact E.congr (funext fun z => by unfold slopeCoefficient multiplierWord; rfl)

noncomputable def slopeValue (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (z : List Bool) :=
  multiply P (pair z (pair (IntegralMixedFramedHeightScaleFactorBits.factor P D J z) (slopeCoefficient P D J h z)))

attribute [local irreducible] slopeValue

theorem slopeValue_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : SpaceFunction (slopeValue P D J h) := by
  have E := ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedFramedHeightScaleFactorBits.factor_space_low P a D J h.low).pairOutputs
    (slopeCoefficient_space P a D J h))).postcompose (multiply P) (multiply_FP P a)
  exact E.congr (funext fun z => by unfold slopeValue; rfl)

noncomputable def post (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (z : List Bool) :=
  if guard P z then if constantBranch P z then IntegralMixedFramedHeightPostBits.constantValue P D J z
  else if slopeBranch P z then slopeValue P D J h z else [] else []

theorem post_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) : SpaceFunction (post P D J h) := by
  have E := SpaceFunction.branch _ (guard_FP P a).flag_mem_FP
    (SpaceFunction.branch _ (constantBranch_FP P a).flag_mem_FP (IntegralMixedFramedHeightPostBits.constantValue_space_low P a D J h.low)
      (SpaceFunction.branch _ (slopeBranch_FP P a).flag_mem_FP (slopeValue_space P a D J h) (SpaceFunction.ofFP _ (constFn_mem_FP []))))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)

theorem slopeCoefficient_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool) :
    slopeCoefficient P D J h (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q))=
      residueBits (IntegralMixedFramedScalarCellsBits.cell P D J q 3 0 : ZMod (modulus P q)) := by
  unfold slopeCoefficient bankFactor
  simp only [pairFst_pair]
  unfold multiplierWord
  rw [h.slope q]
  split_ifs with hc
  · rw [IntegralMixedFramedHeightBankProductBits.value_table P D J q]
    simp only [multiply,pairFst_pair,pairSnd_pair,IntegralMixedFramedHeightIntegerBits.bank,Int.cast_mul]
    exact ArithmeticBits.mulMod_residueBits (modulus P q)
      (IntegralMixedHistory.commonDenominator (IntegralMixedFramedOldHeightBits.state P D J q) : ZMod (modulus P q))
      (h.multiplier q : ZMod (modulus P q))
  · rw [ArithmeticBits.one_residueBits]
    simp only [multiply,pairFst_pair,pairSnd_pair,one_mul]
    simpa only [one_mul] using ArithmeticBits.mulMod_residueBits (modulus P q) (1 : ZMod (modulus P q))
      (h.multiplier q : ZMod (modulus P q))

theorem post_table (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (q : List Bool) :
    post P D J h (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q))=
      IntegralMixedFramedNativeHeightBits.model P D J q := by
  unfold post IntegralMixedFramedNativeHeightBits.model IntegralMixedFramedHeightPostBits.post
  split_ifs
  · rfl
  · unfold slopeValue IntegralMixedFramedHeightPostBits.slopeValue
    rw [slopeCoefficient_table,IntegralMixedFramedHeightTableArithmeticBits.coefficient_packet]
  all_goals rfl
end LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
