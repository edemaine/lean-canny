/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoordinateInteger
public import LeanCanny.Algebra.CannySubresultantSign

/-!
# Integer signs across all coordinate-recovery branches

The uniform coordinate magnitude budget and modular evaluator certify integer
negativity and full three-way coefficient signs, including both direct linear
branches. Signs at algebraic parameter values require further algorithms.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyCoordinateBits

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open CannySubresultantBits (Family BoundedFamily IntegerAccess)

def negativeLanguage (F : BoundedFamily) : Language := {c | integerCoefficient F.family c < 0}
def positiveLanguage (F : BoundedFamily) : Language := {c | 0 < integerCoefficient F.family c}

noncomputable def signValue (F : BoundedFamily) (c : List Bool) : List Bool :=
  if integerCoefficient F.family c = 0 then [] else if integerCoefficient F.family c < 0 then [true] else [false, true]

theorem value_packet (F : Family) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    value F (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((integerCoefficient F c : ZMod m).val) := by
  unfold value CannyResultantBits.mValue
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (m - 1)) = m - 1 from Nat.fromBitsLE_bits _,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

theorem signEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction (fun c => if integerCoefficient F.family c < 0 then [true] else []) := by
  refine IntegerSignBits.evaluator (evaluator a.residue (a.residue_polyTime ha)) (budgetWord a)
    (budgetWord_mem_FP a ha) (integerCoefficient F.family) ?_ (value_packet F.family)
  intro c
  rw [budgetWord_code, show Nat.fromBitsLE (BinaryNatCode.encode (budget F c)) = budget F c from Nat.fromBitsLE_bits _]
  exact coefficient_bits F c

theorem signDecider {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceDecider (negativeLanguage F) := by
  have hflag : (fun w : List Bool => [w[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply (signEvaluator a ha).decider (fun w => w[0]?.getD false) hflag
  intro c
  by_cases hz : integerCoefficient F.family c < 0 <;> simp [negativeLanguage, hz]

theorem negativeLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    negativeLanguage F ∈ PSPACE := (signDecider a ha).mem_PSPACE

theorem signumEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction (signValue F) := by
  classical
  let N := (signEvaluator a ha).withInput
  let Z := (((integerDecider a ha).indicator).precompose pairFst pairFst_mem_FP).withInput
  let E := (N.chain Z).postcompose CannyResultantBits.signOutput CannyResultantBits.signOutput_mem_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, CannyResultantBits.signOutput, pairFst_pair, pairSnd_pair,
    List.getElem?_cons_zero, Option.getD_some]
  by_cases hz : integerCoefficient F.family c = 0 <;> by_cases hn : integerCoefficient F.family c < 0 <;>
    simp [integerZeroLanguage, signValue, hz, hn]

theorem positiveLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    positiveLanguage F ∈ PSPACE := by
  have hflag : (fun w : List Bool => [decide (w = [false, true])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((signumEvaluator a ha).decider (fun w => decide (w = [false, true])) hflag ?_).mem_PSPACE
  intro c
  by_cases hz : integerCoefficient F.family c = 0
  · simp [positiveLanguage, signValue, hz]
  · by_cases hn : integerCoefficient F.family c < 0
    · have hp : ¬ 0 < integerCoefficient F.family c := by omega
      simp [positiveLanguage, signValue, hz, hn, hp]
    · have hp : 0 < integerCoefficient F.family c := by omega
      simp [positiveLanguage, signValue, hz, hn, hp]

end LeanCanny.Algebra.CannyCoordinateBits
