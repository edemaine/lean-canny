/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankScalars

/-! # Implicit polynomial tests at actual retained-bank coordinates

A retained coordinate is its raw joint variable raised to the fixed power
schedule, multiplied by its cofactor and divided by the same common Q.
The resulting integer test has native coefficient, degree and mass access.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankUnivariateSource
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

noncomputable def power (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (q : List Bool) : ℕ :=
  UniformIntegralPowerSchedule.birth (P.cap (pairFst (key q))+1) (2^P.width (pairFst (key q)))
    ((atKey P D H (key q)).count-1-index q)

theorem power_binary (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    {key : List Bool→List Bool} {index : List Bool→ℕ} (hk : key∈FP) (hi : UnaryFn index) :
    BinaryFn (power P D H key index) :=
  UniformIntegralPowerSchedule.birth_binary ((a.cap.comp (mem_FP_comp hk pairFst_mem_FP)).add (UnaryFn.const 1))
    ((BinaryFn.const 2).powUnary (a.width.comp (mem_FP_comp hk pairFst_mem_FP)))
    (((IntegralMixedFramedBankSnapshotBits.count_unary P a D H).comp hk).sub (UnaryFn.const 1) |>.sub hi)

noncomputable def source (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (Q : IntegerPolynomialRootQueriesBits.Source) :=
  IntegerPolynomialRationalPointSource.source Q (IntegralMixedFramedBankScalars.scalars P D H L F C hs key index)
    (power P D H key index)

theorem access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    {L F C : List Bool→ℕ} (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    {key : List Bool→List Bool} {index : List Bool→ℕ} (hk : key∈FP) (hi : UnaryFn index)
    (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q) :
    IntegerPolynomialRootQueriesBits.Access (source P D H L F C hs key index Q) :=
  IntegerPolynomialRationalPointSource.access Q hQ _
    (IntegralMixedFramedBankScalars.access P a D H Hnew c hb hL hF hC hs hk (BinaryFn.ofUnary hi))
    (power_binary P a D H hk hi) (fun _=>UniformIntegralPowerSchedule.birth_pos _ _ _)

end LeanCanny.Algebra.IntegralMixedFramedBankUnivariateSource
