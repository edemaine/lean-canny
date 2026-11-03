/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineSpace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineMatrix
/-! # Source-local affine tables do not depend on the parent's phase tag -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedCurrentQNativeBits.machine
  IntegralMixedFramedHeightAffineSumBits.value IntegralMixedFramedHeightBankProductBits.value table

theorem table_value_at (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hx : 1≤get P .slot15 q ∧ get P .slot15 q≤4) :
    table P D (IntegralMixedFramedCurrentQNativeBits.machine P a D J c).model q=
      IntegralMixedFramedHeightTablePassBits.value P D J q := by
  have HP:=IntegralMixedFramedCurrentQNativeBits.producer_actual P a D J c _ (fun _ _=>rfl)
  have HH:=IntegralMixedFramedCurrentQScalarBits.height_matches P a D J c.scalar _
    (IntegralMixedFramedCurrentQNativeBits.scalar_matches P a D J c _ (fun _ _=>rfl))
  have HE : IntegralMixedFramedHeightTablePassBits.RepliesAt P D J (IntegralMixedFramedHeaderBits.routing P D)
      (IntegralMixedFramedCurrentQNativeBits.machine P a D J c).model q := by
    refine ⟨IntegralMixedFramedHeightCurrentBits.leading_replies P D J _ HP q hv,?_⟩
    intro i _
    apply HH.height _ (IntegralMixedHeightTableQueryBits.writer_selected P q i hv)
    have HE : get P .slot15 (IntegralMixedHeightTableQueryBits.writer P (pair q (BinaryNatCode.encode i)))=get P .slot15 q := by
      rw [IntegralMixedHeightTableQueryBits.writer_get]
      rfl
    rwa [HE]
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

theorem value_matrix_at (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hx : 1≤get P .slot15 q ∧ get P .slot15 q≤4) :
    value P a D J c q=residueBits
      (Algebra.leftMulMatrix (IntegralMixedFramedOldHeightBits.state P D J q).sampler.scalarPrefix.basis.finBasis
        (IntegralMixedHistory.expression (IntegralMixedFramedOldHeightBits.state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q))
        (IntegralMixedFramedHeightTableMatrixBits.row P D J q) (IntegralMixedFramedHeightTableMatrixBits.col P D J q) : ZMod (modulus P q)) := by
  rw [value,output,table_value_at P a D J c q hv hx,IntegralMixedFramedHeightTableArithmeticBits.affine_table,affine_matrix]

noncomputable def common (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J) (q : List Bool) :=
  IntegralMixedFramedHeightBankProductBits.value P
    (pair q (table P D (IntegralMixedFramedCurrentQNativeBits.machine P a D J c).model q))

theorem common_space (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds P D J c) : SpaceFunction (common P a D J c) :=
  by
    unfold common
    exact (table_space P a D J c hb).withInput.postcompose _ (IntegralMixedFramedHeightBankProductBits.value_FP P a)

theorem common_actual_at (P : Parameters) (a : Access P) (D : Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (c : IntegralMixedFramedCurrentQNativeBits.Controls P D J)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hx : 1≤get P .slot15 q ∧ get P .slot15 q≤4) :
    common P a D J c q=residueBits (IntegralMixedHistory.commonDenominator (IntegralMixedFramedOldHeightBits.state P D J q) : ZMod (modulus P q)) := by
  rw [common,table_value_at P a D J c q hv hx]
  exact IntegralMixedFramedHeightTableArithmeticBits.bank_table P D J q

end LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineBits
