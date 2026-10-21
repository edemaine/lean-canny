/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzSpaceEntries

/-! # Scalar determinant residues from space-bounded entry access

The existing power evaluator returns the constant characteristic coefficient.
An FP parity correction gives the determinant itself, including dimension zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits (F.matrix c).det

namespace ModularAccess

def determinantOutput {F : ModularFamily} (a : ModularAccess F) (z : List Bool) : List Bool :=
  if BinaryNat.mod (pair (a.access.dimension (pairFst z)) (BinaryNatCode.encode 2)) = []
  then pairSnd z
  else ArithmeticBits.negate (pair (a.access.modulus (pairFst z)) (pairSnd z))

theorem determinantOutput_mem_FP {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    determinantOutput a ∈ FP := by
  have hn := mem_FP_comp pairFst_mem_FP ha.dimension
  have hp := mem_FP_comp (mem_FP_pair hn (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.mod_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP ha.modulus
  have hneg := mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  have h := (stringEq_fppred hp (constFn_mem_FP [])).ite_mem_FP pairSnd_mem_FP hneg
  refine mem_FP_of_eq (g := determinantOutput a) h ?_
  intro z
  simp only [Function.comp_apply, determinantOutput]

theorem determinantOutput_pair {F : ModularFamily} (a : ModularAccess F) (c : List Bool)
    (x : ZMod (F.modulus c)) : determinantOutput a (pair c (residueBits x)) =
      residueBits ((-1) ^ F.dimension c * x) := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  rw [determinantOutput, pairFst_pair, pairSnd_pair, (a.correct c).dimension, (a.correct c).modulus]
  simp only [BinaryNat.mod_pair, QueryBits.code_value, BinaryNat.bits_eq_nil_iff]
  rw [neg_one_pow_eq_pow_mod_two]
  by_cases he : F.dimension c % 2 = 0
  · simp [he]
  · have ho : F.dimension c % 2 = 1 := by
      have h := Nat.mod_lt (F.dimension c) (by decide : 0 < 2)
      omega
    simp [ho, ArithmeticBits.negate_residueBits]

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.access.entry) : SpaceFunction F.value := by
  let Q := (powerEvaluator a ha E).withInput.postcompose (determinantOutput a)
    (determinantOutput_mem_FP a ha)
  refine Q.congr (funext fun c => ?_)
  simp only [Function.comp_apply]
  change determinantOutput a (pair c (residueBits ((powerMatrix (F.matrix c) ^ F.dimension c)
    (powerQuery (F.dimension c) 0).row (powerQuery (F.dimension c) 0).col))) = _
  rw [determinantOutput_pair]
  exact congrArg residueBits (det_eq_powerMatrix (F.matrix c)).symm

end ModularAccess
end LeanCanny.Algebra.Berkowitz
