/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateHead
public import LeanCanny.Algebra.IntegralMixedFramedCoordinatePackedMass
/-! # Ordinary original-source coefficient access on the same terminal tuple -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateHeadBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask MatrixPower
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCoordinateBivariateBits (nativeWidth)
open IntegralMixedFramedBankSnapshotBits (atKey)
open RationalSubstitution.IntegerBits (context selectedDegree context_mem_FP selectedDegree_mem_FP)
open scoped Classical
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem polynomial_comp (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (read : List Bool→List Bool) (q : List Bool) :
    polynomial P D H (parent ∘ read) (terminal ∘ read) (d ∘ read) (e ∘ read) q=
      polynomial P D H parent terminal d e (read q) :=rfl

noncomputable def sourceValue (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) :=
  FixedWidthRowBits.value (fun q=>(atKey P D H (terminal (context q))).count+1)
    (fun q=>nativeWidth P D H parent e (context q))
    (fun q=>(polynomial P D H parent terminal d e (context q)).coeff (y (context q))) selectedDegree pairSnd

theorem source_evaluator (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (I : IntegralMixedVirtualQueryBits.InputMetadata (family P D H))
    (h : IntegralMixedFramedCurrentQNativeBits.Controls (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C))
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (IntegralMixedFramedCutProbeTaskBits.parameters P L F C)
      (IntegralMixedFramedCutProbeTransportBits.plan P D L F C) (IntegralMixedFramedCutProbeTransportBits.data P D H L F C) h)
    (parent terminal : List Bool→List Bool) (hp : parent∈FP) (ht : terminal∈FP)
    (d e y : List Bool→ℕ) (hd : BinaryFn d) (he : BinaryFn e) (hy : BinaryFn y) :
    SpaceFunction (sourceValue P D H parent terminal d e y) :=by
  have E:=coefficient_evaluator P a D H L F C hL hF hC I h hb
    (parent ∘ context) (terminal ∘ context) (mem_FP_comp context_mem_FP hp) (mem_FP_comp context_mem_FP ht)
    (d ∘ context) (e ∘ context) (y ∘ context) (hd.comp context_mem_FP) (he.comp context_mem_FP) (hy.comp context_mem_FP)
    selectedDegree pairSnd selectedDegree_mem_FP pairSnd_mem_FP
  refine E.congr (funext fun q=>?_)
  unfold FixedWidthRowBits.value sourceValue
  have HE:=polynomial_comp P D H parent terminal d e context q
  change residueBits ((((polynomial P D H (parent ∘ context) (terminal ∘ context) (d ∘ context) (e ∘ context) q).coeff
      (y (context q))).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _)
        (nativeWidth P D H (parent ∘ context) (e ∘ context) q) (Nat.fromBitsLE (selectedDegree q))) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd q)+1))=_
  rw [HE]
  rfl

private noncomputable def sourceEntry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (c : List Bool) (u : ℕ) (mw : List Bool) :=
  residueBits (((((polynomial P D H parent terminal d e c).coeff (y c)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (nativeWidth P D H parent e c) u)) : ℤ) :
    ZMod (Nat.fromBitsLE mw+1))

private theorem sourceValue_entry (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (q : List Bool) :
    sourceValue P D H parent terminal d e y q=
      sourceEntry P D H parent terminal d e y (context q) (Nat.fromBitsLE (selectedDegree q)) (pairSnd q) :=rfl

private theorem sourceEntry_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (c : List Bool) (u : ℕ) (mw : List Bool) :
    sourceEntry P D H parent terminal d e y c u mw=residueBits
      (((((polynomial P D H parent terminal d e c).coeff (y c)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (nativeWidth P D H parent e c) u)) : ℤ) :
          ZMod (Nat.fromBitsLE mw+1)) :=rfl

attribute [local irreducible] sourceEntry

theorem source_packet (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (c : List Bool) (r m : ℕ) (hm : 0<m) :
    sourceValue P D H parent terminal d e y (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m-1)))=
      residueBits (((((polynomial P D H parent terminal d e c).coeff (y c)).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (nativeWidth P D H parent e c) r)) : ℤ) : ZMod m) :=by
  rw [sourceValue_entry]
  have HE:=sourceEntry_value P D H parent terminal d e y c r (BinaryNatCode.encode (m-1))
  have HM : Nat.fromBitsLE (BinaryNatCode.encode (m-1))+1=m:=by simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits];omega
  rw [HM] at HE
  rw [←HE]
  simp only [RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem source_fit (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (parent terminal : List Bool→List Bool) (d e y : List Bool→ℕ) (c : List Bool)
    (i : Fin ((atKey P D H (terminal c)).count+1)) :
    ((polynomial P D H parent terminal d e c).coeff (y c)).degreeOf i<2^nativeWidth P D H parent e c :=
  ((MvPolynomial.degreeOf_le_totalDegree _ i).trans
    (coefficient_degree P D H parent terminal d e c (y c))).trans_lt (Nat.lt_size_self _)

theorem coefficient_mass (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hF : ∀ root,1≤F root)
    (hf : ∀ key,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key)
    (parent terminal : List Bool→List Bool) (d e : List Bool→ℕ) (c : List Bool) (y : ℕ) :
    MvMass.mass ((polynomial P D H parent terminal d e c).coeff y)≤
      2^IntegralMixedFramedCoordinatePackedBits.headMassBound P D H L F C parent e c :=by
  unfold polynomial
  split_ifs
  · rw [castHead,Polynomial.coeff_map,IntegralMixedFramedCoordinateParameterSuffixBits.polynomial,
      FixedWidthBivariateParameterSuffixBits.coefficient]
    exact (MvMass.rename_le _ _).trans ((MvMass.rename_le _ _).trans
      (IntegralMixedFramedCoordinatePackedBits.guardedHead_mass P D H L F C hs hF hf parent d e c y))
  · simp

end LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateHeadBits
