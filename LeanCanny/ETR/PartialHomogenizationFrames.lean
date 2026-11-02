/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.ETR.PartialHomogenizationNative
public import LeanCanny.ETR.PartialHomogenizationStackBounds

/-! # Semantic frames and readback for the native homogenization pass -/
@[expose] public section
namespace LeanCanny.ETR.PartialHomogenizationNative
open LeanCanny.Encoding
open PartialHomogenizationData Brackets

def code (P : Parameters) (z : List Bool) (xs : List Data) : List Bool :=
  frameCode (P.parameterCount z) (P.degree z) (P.limit z) xs

theorem degreeFinish_code (P : Parameters) (z : List Bool) (xs : List Data) :
    degreeFinish P (pair z (code P z xs)) = degree (P.parameterCount z) (P.degree z) (.l xs) := by
  rcases xs with _ | ⟨tag,_ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩⟩ <;>
    simp [degreeFinish,code,frameCode,context,frame,raw,degrees,leftDegree,rightDegree,variableIndex,
      NNF.hasOne_toBits,NNF.hasTwo_toBits,NNF.one,NNF.two,NNF.second,NNF.third,
      remainingChildren_toBits,firstChild_toBits,degree,Codec.unaryValue,Data.length_toBits]

theorem termFinish_code (P : Parameters) (z : List Bool) (xs : List Data) :
    termFinish P (pair z (code P z xs)) =
      (bounded (P.parameterCount z) (P.degree z) (P.limit z) (.l xs)).toBits := by
  by_cases HL : (Data.l xs).size ≤ P.limit z
  · rw [bounded,ite_eq_left HL]
    have HC : ∀ a ∈ xs, a.size ≤ P.limit z := fun a ha =>
      (Data.size_lt_of_mem ha).le.trans HL
    rcases xs with _ | ⟨tag,_ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩⟩
    all_goals
      simp only [termFinish,code,frameCode,context,frame,raw,terms,pairFst_pair,pairSnd_pair,
        Data.length_toBits,HL,ite_true]
      simp [NNF.hasOne_toBits,NNF.hasTwo_toBits,NNF.one,NNF.two,NNF.second,NNF.third,
        remainingChildren_toBits,firstChild_toBits,variableIndex,leftPower,rightPower,leftDegree,rightDegree,
        frame,raw,degrees,Codec.unaryValue,Data.length_toBits,Codec.unary_size,
        bounded,PartialHomogenizationData.raw,HC,Term.toData]
    all_goals split_ifs <;> rfl
  · simp [termFinish,code,frameCode,context,frame,raw,Data.length_toBits,HL,bounded]

end LeanCanny.ETR.PartialHomogenizationNative
