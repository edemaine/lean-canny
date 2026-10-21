/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannySubresultantInteger
public import LeanCanny.Algebra.CannyResultantSign

/-!
# Integer signs of Canny's numerator and denominator coefficients

The actual integer coefficients have certified uniform residue access and a
binary magnitude budget. Streamed sign recovery and integer zero testing give
a full three-way sign evaluator without materializing a coefficient.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannySubresultantBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def BoundedFamily.negativeLanguage (F : BoundedFamily) : Language := {c | F.family.integerCoefficient c < 0}
def BoundedFamily.positiveLanguage (F : BoundedFamily) : Language := {c | 0 < F.family.integerCoefficient c}

/-- Canonical tags: zero is `0`, negative is `1`, and positive is `2`. -/
noncomputable def BoundedFamily.signValue (F : BoundedFamily) (c : List Bool) : List Bool :=
  if F.family.integerCoefficient c = 0 then [] else if F.family.integerCoefficient c < 0 then [true] else [false, true]

theorem Family.value_packet (F : Family) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    F.value (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((F.integerCoefficient c : ZMod m).val) := by
  unfold Family.value CannyResultantBits.mValue
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (m - 1)) = m - 1 from Nat.fromBitsLE_bits _,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

namespace IntegerAccess

theorem signEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction (fun c => if F.family.integerCoefficient c < 0 then [true] else []) := by
  refine IntegerSignBits.evaluator (Access.evaluator a.residue (residue_polyTime a ha)) a.source.budget
    (a.source.budget_mem_FP ha.source) F.family.integerCoefficient ?_ F.family.value_packet
  intro c
  rw [a.source.budget_code, show Nat.fromBitsLE (BinaryNatCode.encode (F.source.budget c)) = F.source.budget c
    from Nat.fromBitsLE_bits _]
  exact F.coefficient_bits c

theorem signDecider {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceDecider F.negativeLanguage := by
  have hflag : (fun w : List Bool => [w[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply (signEvaluator a ha).decider (fun w => w[0]?.getD false) hflag
  intro c
  by_cases hz : F.family.integerCoefficient c < 0 <;> simp [BoundedFamily.negativeLanguage, hz]

theorem negativeLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.negativeLanguage ∈ PSPACE := (signDecider a ha).mem_PSPACE

theorem signumEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction F.signValue := by
  classical
  let N := (signEvaluator a ha).withInput
  let Z := (((decider a ha).indicator).precompose pairFst pairFst_mem_FP).withInput
  let E := (N.chain Z).postcompose CannyResultantBits.signOutput CannyResultantBits.signOutput_mem_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, CannyResultantBits.signOutput, pairFst_pair, pairSnd_pair,
    List.getElem?_cons_zero, Option.getD_some]
  by_cases hz : F.family.integerCoefficient c = 0 <;> by_cases hn : F.family.integerCoefficient c < 0 <;>
    simp [BoundedFamily.zeroLanguage, BoundedFamily.signValue, hz, hn]

theorem positiveLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.positiveLanguage ∈ PSPACE := by
  have hflag : (fun w : List Bool => [decide (w = [false, true])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((signumEvaluator a ha).decider (fun w => decide (w = [false, true])) hflag ?_).mem_PSPACE
  intro c
  by_cases hz : F.family.integerCoefficient c = 0
  · simp [BoundedFamily.positiveLanguage, BoundedFamily.signValue, hz]
  · by_cases hn : F.family.integerCoefficient c < 0
    · have hp : ¬ 0 < F.family.integerCoefficient c := by omega
      simp [BoundedFamily.positiveLanguage, BoundedFamily.signValue, hz, hn, hp]
    · have hp : 0 < F.family.integerCoefficient c := by omega
      simp [BoundedFamily.positiveLanguage, BoundedFamily.signValue, hz, hn, hp]

end IntegerAccess
end LeanCanny.Algebra.CannySubresultantBits
