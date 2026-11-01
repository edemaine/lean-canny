/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerObjectiveSpace
public import LeanCanny.Computation.TwoCallController

/-! # Resumable Euler objective coefficients

The two children supply the actual frozen lower coefficient and the Euler
sum. Native degree multiplication and modular subtraction combine them.
Neither child's computation is assumed by the controller certificate.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits.ObjectiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] subtractPost IntegralCriticalLeadingBits.degreePost

noncomputable def post (S : Source) (z : List Bool) : List Bool :=
  subtractPost S (pair (pairFst z) (pair
    (IntegralCriticalLeadingBits.degreePost S.toGradient.toFrozen (pair (pairFst z) (pairFst (pairSnd z))))
    (pairSnd (pairSnd z))))

theorem post_FP (S : Source) (a : Access S) : post S ∈ FP := by
  have HL := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have HR := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have HD := mem_FP_comp (mem_FP_pair pairFst_mem_FP HL)
    (IntegralCriticalLeadingBits.degreePost_FP S.toGradient.toFrozen a.toGradient.toFrozen)
  exact mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair HD HR)) (subtractPost_FP S a)

noncomputable def program (S : Source) (lowerTask sumTask : List Bool → List Bool) : RecursiveFold.Program :=
  TwoCall.program lowerTask sumTask (post S)

theorem certificates (S : Source) (a : Access S) (lowerTask sumTask : List Bool → List Bool)
    (hl : lowerTask ∈ FP) (hs : sumTask ∈ FP) :
    (program S lowerTask sumTask).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  TwoCall.certificates lowerTask sumTask (post S) hl hs (post_FP S a)

attribute [local irreducible] Source.objectiveValue Source.sumValue IntegralFrozenPowerBits.Source.lowerValue

theorem value_eq (S : Source) (lowerTask sumTask answer : List Bool → List Bool)
    (hl : ∀ c, answer (lowerTask c) = S.toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (sumTask c) = S.sumValue c) (c : List Bool) :
    (program S lowerTask sumTask).value answer c = S.objectiveValue c := by
  change (TwoCall.program lowerTask sumTask (post S)).value answer c = _
  rw [TwoCall.value_eq, hl c, hs c]
  unfold post
  simp only [pairFst_pair, pairSnd_pair]
  exact objective_value S c

theorem output_when_halted (S : Source) (lowerTask sumTask answer : List Bool → List Bool)
    (hl : ∀ c, answer (lowerTask c) = S.toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (sumTask c) = S.sumValue c) (c : List Bool) (t : ℕ)
    (hh : (program S lowerTask sumTask).controller.halted
      (((program S lowerTask sumTask).controller.reference answer)^[t] ((program S lowerTask sumTask).initial c)) = true) :
    (program S lowerTask sumTask).controller.output
      (((program S lowerTask sumTask).controller.reference answer)^[t] ((program S lowerTask sumTask).initial c)) = S.objectiveValue c :=
  ((program S lowerTask sumTask).output_when_halted answer c t hh).trans (value_eq S lowerTask sumTask answer hl hs c)

theorem requests_iff (S : Source) (lowerTask sumTask answer : List Bool → List Bool) (c child : List Bool) :
    (program S lowerTask sumTask).controller.Requests answer (fun _ => 2) c child ↔
      child = lowerTask c ∨ child = sumTask c :=
  TwoCall.requests_iff lowerTask sumTask (post S) answer c child

theorem state_length (S : Source) (lowerTask sumTask answer : List Bool → List Bool)
    (hl : ∀ c, answer (lowerTask c) = S.toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (sumTask c) = S.sumValue c) (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program S lowerTask sumTask).controller.reference answer)^[t]
      ((program S lowerTask sumTask).initial c))).length ≤
        2 * c.length + 2 * (encNat 2).length + (BinaryNatCode.encode (S.modulus c)).length + 2 := by
  let : NeZero (S.modulus c) := ⟨S.modulus_ne_zero c⟩
  have HB (x : ZMod (S.modulus c)) : (residueBits x).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    apply ModularFold.bits_length_le (fun _ => BinaryNatCode.encode (S.modulus c)) c x.val
    simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using ZMod.val_lt x
  have HL : (S.toGradient.toFrozen.lowerValue c).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    unfold IntegralFrozenPowerBits.Source.lowerValue
    exact HB _
  have HO : (S.objectiveValue c).length ≤ (BinaryNatCode.encode (S.modulus c)).length := by
    unfold Source.objectiveValue
    exact HB _
  have HP : post S (pair c (pair (S.toGradient.toFrozen.lowerValue c) (S.sumValue c))) = S.objectiveValue c := by
    unfold post
    simp only [pairFst_pair, pairSnd_pair]
    exact objective_value S c
  have H := TwoCall.state_length lowerTask sumTask (post S) answer c t
  rw [hl c, hs c, HP] at H
  exact H.trans (by omega)

end LeanCanny.Algebra.IntegralEulerBits.ObjectiveStage
