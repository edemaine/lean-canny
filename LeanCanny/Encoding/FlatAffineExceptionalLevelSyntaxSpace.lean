/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalRawHeightSyntax
public import LeanCanny.Algebra.IntegralMixedAffineSyntaxSpace
/-! # Original charged level records produce literal actual affine syntax -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def leftStage (F : Inputs) (input : List Bool → List Bool) (p : List Bool) :=
  min (Nat.fromBitsLE (FlatAffineFullSourceTower.left (pairSnd p))) (F.depth (input (pairFst p)) - 1)
def rightStage (F : Inputs) (input : List Bool → List Bool) (p : List Bool) :=
  min (Nat.fromBitsLE (FlatAffineFullSourceTower.right (pairSnd p))) (F.depth (input (pairFst p)) - 1)

def levelKernel (F : Inputs) (input : List Bool → List Bool) (p : List Bool) :=
  let u := input (pairFst p)
  let r := pairSnd p
  let v := FlatAffineFullSourceTower.normal r
  let c := FlatAffineFullSourceTower.integer (F.width u) (FlatAffineFullSourceTower.constant r) 0
  if 0 < F.depth u then
    if FlatAffineFullSourceTower.tag r = 1 then IntegralMixedAffineCode.encode (rawHeight F u (leftStage F input p) v)
    else if FlatAffineFullSourceTower.tag r = 2 then IntegralMixedAffineCode.encode
      (.add (rawHeight F u (leftStage F input p) v) (rawHeight F u (rightStage F input p) v))
    else IntegralMixedAffineCode.encode (.constant c)
  else IntegralMixedAffineCode.encode (.constant c)

theorem levelKernel_FP {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP) :
    levelKernel F input ∈ FP := by
  have HU := mem_FP_comp pairFst_mem_FP hi
  have HK := hF.depth.comp HU
  have HW := hF.width.comp HU
  have HLeft : (fun p => FlatAffineFullSourceTower.left (pairSnd p)) ∈ FP := by polytime [FlatAffineFullSourceTower.left]
  have HRight : (fun p => FlatAffineFullSourceTower.right (pairSnd p)) ∈ FP := by polytime [FlatAffineFullSourceTower.right]
  have HNormal : (fun p => FlatAffineFullSourceTower.normal (pairSnd p)) ∈ FP := by polytime [FlatAffineFullSourceTower.normal]
  have HConstant : (fun p => FlatAffineFullSourceTower.constant (pairSnd p)) ∈ FP := by polytime [FlatAffineFullSourceTower.constant]
  have HL : UnaryFn (leftStage F input) := UnaryFn.fromBitsLE_min HLeft (HK.sub (UnaryFn.const 1))
  have HR : UnaryFn (rightStage F input) := UnaryFn.fromBitsLE_min HRight (HK.sub (UnaryFn.const 1))
  have HA := rawHeight_encode_FP hF (fun p => input (pairFst p)) HU (leftStage F input) HL _ HNormal
  have HB := rawHeight_encode_FP hF (fun p => input (pairFst p)) HU (rightStage F input) HR _ HNormal
  have HAB0 := ETR.Codec.taggedTwo_mem_FP 2 HA HB
  have HAB : (fun p => IntegralMixedAffineCode.encode (.add
      (rawHeight F (input (pairFst p)) (leftStage F input p) (FlatAffineFullSourceTower.normal (pairSnd p)))
      (rawHeight F (input (pairFst p)) (rightStage F input p) (FlatAffineFullSourceTower.normal (pairSnd p))))) ∈ FP :=
    mem_FP_of_eq HAB0 (fun p => by simp only [IntegralMixedAffineCode.encode, IntegralMixedAffineCode.term, ETR.Term.add_toBits])
  have HC0 := mem_FP_comp (f := IntegralMixedAffineCode.signedSlice (fun p => F.width (input (pairFst p))) (fun _ => 0)
      (fun p => FlatAffineFullSourceTower.constant (pairSnd p))) (g := IntegralMixedAffineCode.integerLiteral)
    (IntegralMixedAffineCode.signedSlice_FP _ _ _ HW (UnaryFn.const 0) HConstant) IntegralMixedAffineCode.integerLiteral_FP
  have HC : (fun p => IntegralMixedAffineCode.encode (.constant
      (FlatAffineFullSourceTower.integer (F.width (input (pairFst p))) (FlatAffineFullSourceTower.constant (pairSnd p)) 0))) ∈ FP :=
    mem_FP_of_eq HC0 (fun p => by simp only [Function.comp_apply, IntegralMixedAffineCode.integerLiteral_eq,
      IntegralMixedAffineCode.signedSlice_value, IntegralMixedAffineCode.encode, IntegralMixedAffineCode.term])
  have HT : BinaryFn (fun p => FlatAffineFullSourceTower.tag (pairSnd p)) :=
    BinaryFn.fromBits (take_mem_FP (drop_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (UnaryFn.const 1)) (UnaryFn.const 2))
  exact ((BinaryFn.const 0).lt (BinaryFn.ofUnary HK)).ite_mem_FP
    ((HT.eq (BinaryFn.const 1)).ite_mem_FP HA ((HT.eq (BinaryFn.const 2)).ite_mem_FP HAB HC)) HC

theorem levelKernel_packet (F : Inputs) (input : List Bool → List Bool) (q : List Bool) (j : Fin (arity F (input q))) :
    levelKernel F input (pair q (F.level (FlatAffineFullSourceTower.levelQuery (input q) (F.depth (input q)) j.val))) =
      IntegralMixedAffineCode.encode (level F (input q) (FlatAffineFullSourceTower.level F (input q) (F.depth (input q)) j)) := by
  unfold levelKernel leftStage rightStage FlatAffineFullSourceTower.level
  simp only [pairFst_pair, pairSnd_pair]
  split_ifs <;> simp only [level, rawHeight, height, spatialIndex_val]

theorem level_encode_space {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (J : (q : List Bool) → Fin (arity F (input q))) (hj : SpaceFunction (fun q => BinaryNatCode.encode (J q).val)) :
    SpaceFunction (fun q => IntegralMixedAffineCode.encode
      (level F (input q) (FlatAffineFullSourceTower.level F (input q) (F.depth (input q)) (J q)))) := by
  have HK := (BinaryFn.ofUnary (hF.depth.comp hi)).bits_mem_FP
  have HQ := (SpaceFunction.ofFP _ (mem_FP_pair hi HK)).pairOutputs hj
  have HR := HQ.chain hF.level
  have H := HR.withInput.postcompose (levelKernel F input) (levelKernel_FP hF input hi)
  apply H.congr
  funext q
  exact levelKernel_packet F input q (J q)

theorem shifted_encode_space {F : Inputs} (hF : F.Access) (input : List Bool → List Bool) (hi : input ∈ FP)
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (J : (q : List Bool) → Fin (arity F (input q))) (hj : BinaryFn (fun q => (J q).val)) :
    SpaceFunction (fun q => IntegralMixedAffineCode.encode (shifted F h (input q) (J q))) := by
  have HL := level_encode_space hF input hi J (SpaceFunction.ofFP _ hj.bits_mem_FP)
  have HP := hj.eq (hh.comp hi)
  have HB := HP.ite_mem_FP (constFn_mem_FP (IntegralMixedAffineCode.encode (.reference 0)))
    (constFn_mem_FP (IntegralMixedAffineCode.encode (.constant 0)))
  have HT := ETR.Codec.taggedTwo_mem_FP 2 pairFst_mem_FP pairSnd_mem_FP
  have E := (HL.pairOutputs (SpaceFunction.ofFP _ HB)).postcompose _ HT
  apply E.congr
  funext q
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, shifted, IntegralMixedAffineCode.encode,
    IntegralMixedAffineCode.term, ETR.Term.add_toBits]
  have HE : (J q).val = (h (input q)).val ↔ J q = h (input q) := Fin.ext_iff.symm
  simp only [HE]
  split_ifs <;> rfl
end LeanCanny.Encoding.FlatAffineExceptionalMixedExpressions
