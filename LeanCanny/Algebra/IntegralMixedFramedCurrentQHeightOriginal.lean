/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightCosts
public import LeanCanny.Algebra.IntegralMixedAffineSyntaxSpace
public import LeanCanny.Algebra.IntegralMixedFramedAffineScalarSnapshot
/-! # Original syntax supplies affine cells and literal scales without slope Q

The encoded body is original affine syntax. Scale flags select one or two;
no residue reader for an interpreted bank is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] modulus IntegralMixedFramedScalarCellsBits.cell IntegralMixedFramedScalarCellsBits.affine

structure OriginalCells (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  word : List Bool → List Bool
  word_space : SpaceFunction word
  word_eq : ∀ q,word q=IntegralMixedAffineCode.encode (IntegralMixedFramedScalarCellsBits.affine P D J q)
  double : List Bool → Bool
  double_FP : (fun q => [double q])∈FP
  scales : ∀ q i,IntegralMixedFramedScalarCellsBits.cell P D J q 2 i=
    IntegralMixedFramedAffineScalarBits.literalScale P double q i

theorem read_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (tag : ℕ) (p : List Bool) :
    IntegralMixedFramedHeightCellAccessBits.read P D J tag p=
      residueBits (IntegralMixedFramedScalarCellsBits.cell P D J (pairFst (pairFst p)) tag (Nat.fromBitsLE (pairSnd p)) :
        ZMod (modulus P (pairFst (pairFst p)))) := by
  unfold IntegralMixedFramedHeightCellAccessBits.read IntegralMixedFramedScalarCellsBits.reader
  apply congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
  · simp only [IntegralMixedFramedHeightCellAccessBits.query,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  · exact congrArg (modulus P) (pairFst_pair _ _)

theorem lowControls (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : OriginalCells P D J) : LowControls P D J := by
  let Q := fun p => pairFst (pairFst p)
  have HQ : Q∈FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HM : BinaryFn (fun p => modulus P (Q p)) := (modulus_binary P a).comp HQ
  have HB := h.word_space.precompose Q HQ
  have HC := IntegralMixedAffineCode.constant_space_fromSpace
    (fun p => IntegralMixedFramedScalarCellsBits.affine P D J (Q p)) (h.word ∘ Q)
    (fun p => BinaryNatCode.encode (modulus P (Q p)-1)) HB
    ((HM.sub (BinaryFn.const 1)).bits_mem_FP) (fun p => h.word_eq (Q p))
  have HR := IntegralMixedAffineCode.reference_space_fromSpace
    (fun p => IntegralMixedFramedScalarCellsBits.affine P D J (Q p)) (h.word ∘ Q)
    (fun p => BinaryNatCode.encode (modulus P (Q p)-1)) (fun p => Nat.fromBitsLE (pairSnd p)) HB
    ((HM.sub (BinaryFn.const 1)).bits_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP) (fun p => h.word_eq (Q p))
  have Hmod : ∀ p,Nat.fromBitsLE (BinaryNatCode.encode (modulus P (Q p)-1))+1=modulus P (Q p) := by
    intro p
    simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]
    have H := modulus_ne_zero P (Q p)
    omega
  constructor
  intro tag htag
  interval_cases tag
  · apply HC.congr
    funext p
    rw [Hmod,read_eq]
    simp only [Q,IntegralMixedFramedScalarCellsBits.cell,Nat.reduceEqDiff,ite_true,ite_false]
  · apply HR.congr
    funext p
    rw [Hmod,read_eq]
    simp only [Q,IntegralMixedFramedScalarCellsBits.cell,Nat.reduceEqDiff,ite_true,ite_false]
  · have HS := (IntegralMixedFramedAffineScalarBits.literal_scale_space P a h.double h.double_FP).precompose
      (fun p => pair (Q p) (pairSnd p)) (mem_FP_pair HQ pairSnd_mem_FP)
    apply HS.congr
    funext p
    rw [read_eq,h.scales]
    exact congrArg₂ (fun (q : List Bool) (i : ℕ) => residueBits
      (IntegralMixedFramedAffineScalarBits.literalScale P h.double q i : ZMod (modulus P q)))
      (pairFst_pair (Q p) (pairSnd p)) (congrArg Nat.fromBitsLE (pairSnd_pair (Q p) (pairSnd p)))
end LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightBits
