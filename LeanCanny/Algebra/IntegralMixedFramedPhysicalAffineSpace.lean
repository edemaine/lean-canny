/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQNativeSpace
public import LeanCanny.Computation.SpaceFunctionChain
/-! # Physical affine-height coefficients from native charged bank tables

This exposes the affine sum before clearing-factor multiplication. Every table
cell is read from the actual native model; only original affine cell costs
remain inside its controls. No modular division or height evaluator is used.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedCurrentQNativeBits.machine

noncomputable def table (P : Parameters) (D : Plan P)
    (answer : List Bool→List Bool) (q : List Bool) :=
  FixedWidthNatVector.encode (IntegralMixedFramedHeightTablePassBits.count P q)
    (IntegralMixedFramedHeightTablePassBits.width P q) (fun i=>Nat.fromBitsLE
      (answer (IntegralMixedFramedHeightTablePassBits.task P (IntegralMixedFramedHeaderBits.routing P D)
        (pair q (BinaryNatCode.encode i)))))

attribute [local irreducible] table IntegralMixedFramedHeightAffineSumBits.value

theorem table_evaluator (P : Parameters) (a : Access P) (D : Plan P)
    (hr : IntegralMixedOldBankCofactorBits.RoutingAccess (IntegralMixedFramedHeaderBits.routing P D))
    (answer : List Bool→List Bool) (E : SpaceFunction answer) : SpaceFunction (table P D answer) := by
  unfold table
  have HT:=IntegralMixedFramedHeightTablePassBits.task_FP P a (IntegralMixedFramedHeaderBits.routing P D) hr
  have ER:=(E.precompose _ HT).postcompose BinaryNat.normalize BinaryNat.normalize_mem_FP
  exact FixedWidthNatVector.encodeEvaluator (IntegralMixedFramedHeightTablePassBits.count P)
    (IntegralMixedFramedHeightTablePassBits.width P) (fun q i=>Nat.fromBitsLE
      (answer (IntegralMixedFramedHeightTablePassBits.task P (IntegralMixedFramedHeaderBits.routing P D)
        (pair q (BinaryNatCode.encode i)))))
    (IntegralMixedFramedHeightTablePassBits.count_unary P a) (IntegralMixedFramedHeightTablePassBits.width_unary P a)
    _ ER (fun q i=>by simp only [Function.comp_apply,BinaryNat.normalize_eq_bits,BinaryNatCode.encode])

theorem table_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c) :
    SpaceFunction (table P D (IntegralMixedFramedCurrentQNativeBits.machine P a D J c).model) :=
  table_evaluator P a D (IntegralMixedFramedCurrentQScalarBits.routingAccess P a D J c.scalar) _
    (IntegralMixedFramedCurrentQNativeBits.model_space P a D J c hb)

theorem table_value (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (hq : IntegralMixedFramedNativeHeightBits.selected P q=true) :
    table P D (IntegralMixedFramedCurrentQNativeBits.machine P a D J c).model q=
      IntegralMixedFramedHeightTablePassBits.value P D J q := by
  have HP:=IntegralMixedFramedCurrentQNativeBits.producer_actual P a D J c _ (fun _ _=>rfl)
  have HH:=IntegralMixedFramedCurrentQScalarBits.height_matches P a D J c.scalar _
    (IntegralMixedFramedCurrentQNativeBits.scalar_matches P a D J c _ (fun _ _=>rfl))
  have HE:=IntegralMixedFramedHeightCurrentBits.replies P D J _ HP HH q hq
  unfold table IntegralMixedFramedHeightTablePassBits.value FixedWidthNatVector.encode
  apply congrArg List.ofFn
  funext k
  have HW : 0<IntegralMixedFramedHeightTablePassBits.width P q := by
    by_contra hn
    have H0 : IntegralMixedFramedHeightTablePassBits.width P q=0 := by omega
    have HK:=k.isLt
    have HE : IntegralMixedFramedHeightTablePassBits.count P q*IntegralMixedFramedHeightTablePassBits.width P q=0 := by rw [H0,Nat.mul_zero]
    omega
  have HI := (Nat.div_lt_iff_lt_mul HW).mpr k.isLt
  dsimp only
  rw [IntegralMixedFramedHeightTablePassBits.task_reply P D J _ _ q HE _ HI]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def output (P : Parameters) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool→List Bool) (q : List Bool) :=
  IntegralMixedFramedHeightAffineSumBits.value P D J (pair q (table P D answer q))

theorem output_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (answer : List Bool→List Bool)
    (h : IntegralMixedFramedCurrentQHeightBits.LowControls P D J)
    (ET : SpaceFunction (table P D answer)) : SpaceFunction (output P D J answer) := by
  have EE:=ET.withInput.chain (IntegralMixedFramedHeightAffineSumBits.value_space_low P a D J h)
  unfold output
  exact EE

noncomputable def value (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) :=
  output P D J (IntegralMixedFramedCurrentQNativeBits.machine P a D J c).model

theorem value_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c) : SpaceFunction (value P a D J c) :=
  output_space P a D J _ c.scalar.height.low (table_space P a D J c hb)

theorem value_actual (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (hq : IntegralMixedFramedNativeHeightBits.selected P q=true) :
    value P a D J c q=residueBits (IntegralMixedFramedHeightIntegerBits.affine P D J q : ZMod (modulus P q)) := by
  rw [value,output,table_value P a D J c q hq]
  exact IntegralMixedFramedHeightTableArithmeticBits.affine_table P D J q

end LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineBits
