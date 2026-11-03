/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineCurrent
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSourcePolynomialSpace
/-! # Physical normal scalars use the actual charged current-bank product -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalNormalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedOldHeightBits (state)
open IntegralMixedPhysicalDenominatorPostBits (rawScaleReader scale scaleAt multiply multiply_FP multiply_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedPhysicalBits.family IntegralMixedFramedPhysicalAffineBits.common multiply BinaryNat.mulMod rawScaleReader

noncomputable def rule (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  (IntegralMixedFramedPhysicalBits.family P D J).rule (IntegralMixedPhysicalTaskBits.saved P q)
noncomputable def scaleValue (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (selected : List Bool→ℕ) (q : List Bool) :=
  rawScaleReader P (IntegralMixedFramedPhysicalBits.family P D J) (pair q (BinaryNatCode.encode (selected q)))

theorem scale_space (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (selected : List Bool→ℕ) (hs : BinaryFn selected) :
    SpaceFunction (scaleValue P D J selected) :=
  c.scalar.physicalScales.precompose _ (mem_FP_pair id_mem_FP hs.bits_mem_FP)

noncomputable def value (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (selected : List Bool→ℕ) (q : List Bool) :=
  multiply P (pair q (pair (IntegralMixedFramedPhysicalAffineBits.common P a D J c q) (scaleValue P D J selected q)))

theorem value_space (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c)
    (selected : List Bool→ℕ) (hs : BinaryFn selected) : SpaceFunction (value P a D J c selected) := by
  have EE:=((IntegralMixedFramedPhysicalAffineBits.common_space P a D J c hb).pairOutputs
    (scale_space P D J c selected hs)).withInput.postcompose (multiply P) (multiply_FP P a)
  unfold value
  exact EE

theorem value_actual (P : Parameters) (a : Access P) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (selected : List Bool→ℕ)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hx : get P .slot15 q=1)
    (hs : selected q<(IntegralMixedFramedPhysicalBits.family P D J).ambient (IntegralMixedPhysicalTaskBits.saved P q)+1) :
    value P a D J c selected q=residueBits
      (IntegralMixedHistory.commonDenominator (state P D J q)*(rule P D J q).scales ⟨selected q,hs⟩ : ZMod (modulus P q)) := by
  have HS : scale P (IntegralMixedFramedPhysicalBits.family P D J) q (selected q)=
      (rule P D J q).scales ⟨selected q,hs⟩ := by
    unfold scale
    split_ifs with h
    · rfl
    · exact False.elim (h hs)
  unfold value scaleValue
  rw [IntegralMixedFramedPhysicalAffineBits.common_actual_at P a D J c q hv (by rw [hx];omega),
    IntegralMixedPhysicalDenominatorPostBits.rawScaleReader_packet]
  have HE : scaleAt P (IntegralMixedFramedPhysicalBits.family P D J) q (selected q)=
      ((rule P D J q).scales ⟨selected q,hs⟩ : ZMod (modulus P q)) :=congrArg (fun z : ℤ=>(z : ZMod (modulus P q))) HS
  rw [HE,multiply_packet]

end LeanCanny.Algebra.IntegralMixedFramedPhysicalNormalBits
