/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePacked
/-! # Native integer MV entries for selected coordinate test circuits

One guarded request extracts E's head block and the raw old-variable tail.
The child is the actual cached coordinate reader. No new coefficient or
algebra-element evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinateCoefficientSpaceBits (Core)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e y W : List Bool→ℕ) (target modulus : List Bool→List Bool) (q : List Bool) :=
  if Core P parent q then residueBits ((((head P D H parent d e q).coeff (y q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W q) (Nat.fromBitsLE (target q))) : ℤ) :
      ZMod (Nat.fromBitsLE (modulus q)+1)) else []

theorem value_eq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent : List Bool→List Bool) (d e y W : List Bool→ℕ) (target modulus : List Bool→List Bool) (q : List Bool) :
    value P D H parent d e y W target modulus q=
      if y q≤d q ∧ parameter W target q≤e q then
        IntegralMixedFramedCoordinateCoefficientSpaceBits.value P D H parent y (parameter W target) W
          (IntegerParameterCoefficientBits.spatial W target) modulus q else [] := by
  by_cases hc : Core P parent q
  · unfold value
    rw [ite_eq_left hc,native_coefficient]
    by_cases hy : y q≤d q
    · rw [ite_eq_left hy]
      by_cases hk : parameter W target q≤e q
      · rw [ite_eq_left hk,ite_eq_left ⟨hy,hk⟩]
        unfold IntegralMixedFramedCoordinateCoefficientSpaceBits.value
        rw [ite_eq_left hc]
        rfl
      · rw [ite_eq_right hk,ite_eq_right (fun h=>hk h.2)]
        simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]
    · rw [ite_eq_right hy,ite_eq_right (fun h=>hy h.1)]
      simp only [Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]
  · unfold value
    rw [ite_eq_right hc]
    split_ifs
    · unfold IntegralMixedFramedCoordinateCoefficientSpaceBits.value
      exact (ite_eq_right hc).symm
    · rfl

attribute [local irreducible] head value

theorem evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent : List Bool→List Bool) (hp : parent∈FP) (d e y W : List Bool→ℕ) (hd : BinaryFn d) (he : BinaryFn e)
    (hy : BinaryFn y) (hW : UnaryFn W) (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (value P D H parent d e y W target modulus) := by
  have HK:=parameter_binary W target hW ht
  have EC:=IntegralMixedFramedCoordinateCoefficientSpaceBits.evaluator P a D H L F C hL hF hC I h hb
    parent hp y (parameter W target) W hy HK hW (IntegerParameterCoefficientBits.spatial W target) modulus
    (IntegerParameterCoefficientBits.spatial_mem_FP W target hW ht) hm
  have E:=SpaceFunction.branch (fun q=>decide (y q≤d q ∧ parameter W target q≤e q))
    ((hy.le hd).and (HK.le he)).flag_mem_FP EC (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q=>by
    simp only [decide_eq_true_eq]
    exact (value_eq P D H parent d e y W target modulus q).symm)

end LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedBits
