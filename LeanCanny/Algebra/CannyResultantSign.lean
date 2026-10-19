/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyResultantInteger
public import LeanCanny.Algebra.IntegerSignSpace
public import LeanCanny.Computation.SpaceDeciderOutput

/-!
# Polynomial-space sign testing of Canny resultant coefficients

The source coefficient bounds and existing binary budget writer supply the
integer magnitude budget. The certified Canny residue evaluator supplies all
small-modulus queries. Integer sign recovery therefore decides negativity of
the actual selected integer coefficient, including zero, without storing it.
Composing this test with the zero decider returns its full three-way sign;
both strict-sign languages belong to PSPACE under the same source contracts.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation

def BoundedFamily.negativeLanguage (F : BoundedFamily) : Language := {c | F.source.coefficient c < 0}
def BoundedFamily.positiveLanguage (F : BoundedFamily) : Language := {c | 0 < F.source.coefficient c}

/-- Canonical tags: zero is `0`, negative is `1`, and positive is `2`. -/
noncomputable def BoundedFamily.signValue (F : BoundedFamily) (c : List Bool) : List Bool :=
  if F.source.coefficient c = 0 then [] else if F.source.coefficient c < 0 then [true] else [false, true]

def signOutput (p : List Bool) : List Bool :=
  if (pairSnd p)[0]?.getD false then []
  else if (pairSnd (pairFst p))[0]?.getD false then [true] else [false, true]

theorem signOutput_mem_FP : signOutput ∈ FP :=
  (FPPred.getBit pairSnd_mem_FP (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP [])
    ((FPPred.getBit (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (UnaryFn.const 0)).ite_mem_FP
      (constFn_mem_FP [true]) (constFn_mem_FP [false, true]))

theorem Family.value_packet (F : Family) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    F.value (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((F.coefficient c : ZMod m).val) := by
  unfold Family.value mValue
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (m - 1)) = m - 1 from Nat.fromBitsLE_bits _,
    Nat.sub_add_cancel (by omega : 1 ≤ m)]
  rfl

namespace IntegerAccess

noncomputable def signEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction (fun c => if F.source.coefficient c < 0 then [true] else []) := by
  refine IntegerSignBits.evaluator (Access.evaluator a.residue ha.residue) a.budget (budget_mem_FP a ha)
    F.source.coefficient ?_ ?_
  · intro c
    rw [budget_code, show Nat.fromBitsLE (BinaryNatCode.encode (F.budget c)) = F.budget c from Nat.fromBitsLE_bits _]
    exact F.coefficient_bits c
  · exact F.source.value_packet

noncomputable def signDecider {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceDecider F.negativeLanguage := by
  have hflag : (fun w : List Bool => [w[0]?.getD false]) ∈ FP :=
    (FPPred.getBit id_mem_FP (UnaryFn.const 0)).flag_mem_FP
  apply (signEvaluator a ha).decider (fun w => w[0]?.getD false) hflag
  intro c
  by_cases hz : F.source.coefficient c < 0 <;> simp [BoundedFamily.negativeLanguage, hz]

theorem negativeLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.negativeLanguage ∈ PSPACE := (signDecider a ha).mem_PSPACE

noncomputable def signumEvaluator {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceFunction F.signValue := by
  classical
  let N := (signEvaluator a ha).withInput
  let Z := (((decider a ha).indicator).precompose pairFst pairFst_mem_FP).withInput
  let E := (N.chain Z).postcompose signOutput signOutput_mem_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, signOutput, pairFst_pair, pairSnd_pair,
    List.getElem?_cons_zero, Option.getD_some]
  by_cases hz : F.source.coefficient c = 0 <;> by_cases hn : F.source.coefficient c < 0 <;>
    simp [BoundedFamily.zeroLanguage, BoundedFamily.signValue, hz, hn]

theorem positiveLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.positiveLanguage ∈ PSPACE := by
  have hflag : (fun w : List Bool => [decide (w = [false, true])]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((signumEvaluator a ha).decider (fun w => decide (w = [false, true])) hflag ?_).mem_PSPACE
  intro c
  by_cases hz : F.source.coefficient c = 0
  · simp [BoundedFamily.positiveLanguage, BoundedFamily.signValue, hz]
  · by_cases hn : F.source.coefficient c < 0
    · have hp : ¬ 0 < F.source.coefficient c := by omega
      simp [BoundedFamily.positiveLanguage, BoundedFamily.signValue, hz, hn, hp]
    · have hp : 0 < F.source.coefficient c := by omega
      simp [BoundedFamily.positiveLanguage, BoundedFamily.signValue, hz, hn, hp]

end IntegerAccess
end LeanCanny.Algebra.CannyResultantBits
