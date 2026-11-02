/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalLevelSyntaxSpace
/-! # Concrete shifted affine cells retain charged original level and selector access -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem shifted_encode_space_source {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (J : (q : List Bool) → Fin (arity F (input q))) (hj : SpaceFunction (fun q => BinaryNatCode.encode (J q).val)) :
    SpaceFunction (fun q => IntegralMixedAffineCode.encode (shifted F h (input q) (J q))) := by
  have HL := level_encode_space hF input hi J hj
  have HHeight : BinaryFn (fun p => (h (input (pairFst p))).val) := (hh.comp hi).comp pairFst_mem_FP
  have HP := (BinaryFn.fromBits pairSnd_mem_FP).eq HHeight
  have HB0 := HP.ite_mem_FP (constFn_mem_FP (IntegralMixedAffineCode.encode (.reference 0)))
    (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0)))
  have HB : SpaceFunction (fun q => if (J q).val = (h (input q)).val then
      IntegralMixedAffineCode.encode (.reference 0) else IntegralMixedAffineCode.encode (.constant 0)) := by
    apply (hj.withInput.postcompose _ HB0).congr
    funext q
    exact congrArg₂ (fun (i k : ℕ) => if i = k then IntegralMixedAffineCode.encode (.reference 0)
        else IntegralMixedAffineCode.encode (.constant 0))
      (by simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
      (congrArg (fun c => (h (input c)).val) (pairFst_pair _ _))
  have HT := ETR.Codec.taggedTwo_mem_FP 2 pairFst_mem_FP pairSnd_mem_FP
  have E := (HL.pairOutputs HB).postcompose _ HT
  apply E.congr
  funext q
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair,
    shifted, IntegralMixedAffineCode.encode, IntegralMixedAffineCode.term, ETR.Term.add_toBits]
  simp only [Fin.ext_iff]
  split_ifs <;> rfl

theorem shifted_constant_space {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (J : (q : List Bool) → Fin (arity F (input q))) (hj : SpaceFunction (fun q => BinaryNatCode.encode (J q).val)) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.constantCoefficient (shifted F h (input q) (J q)) :
      ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  IntegralMixedAffineCode.constant_space_fromSpace (fun q => shifted F h (input q) (J q)) _ mod
    (shifted_encode_space_source hF input hi h hh J hj) hm (fun _ => rfl)

theorem shifted_reference_space {F : Inputs} (hF : F.Access) (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (J : (q : List Bool) → Fin (arity F (input q))) (hj : SpaceFunction (fun q => BinaryNatCode.encode (J q).val))
    (I : List Bool → ℕ) (hI : BinaryFn I) :
    SpaceFunction (fun q => residueBits (IntegralMixedAffineCoefficients.referenceCoefficient (shifted F h (input q) (J q)) (I q) :
      ZMod (Nat.fromBitsLE (mod q) + 1))) :=
  IntegralMixedAffineCode.reference_space_fromSpace (fun q => shifted F h (input q) (J q)) _ mod I
    (shifted_encode_space_source hF input hi h hh J hj) hm hI (fun _ => rfl)
end LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
