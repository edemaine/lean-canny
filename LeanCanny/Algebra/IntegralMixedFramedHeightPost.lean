/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightAffineSum
public import LeanCanny.Algebra.IntegralMixedFramedHeightScaleFactor
/-! # Charged scalar-height postprocessing for physical and nilpotent sources -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightPostBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell Primitive)
open IntegralMixedFramedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] cell modulus

def guard (P : Parameters) (z : List Bool) : Prop :=
  get P .slot8 (pairFst z) < P.ambient (RankedHistoryTask.root (pairFst z)) + 1 ∧
    1 ≤ get P .slot15 (pairFst z) ∧ get P .slot15 (pairFst z) ≤ 4

theorem guard_FP (P : Parameters) (a : Access P) : FPPred (guard P) := by
  have HQ := pairFst_mem_FP
  have HI : BinaryFn (fun z => get P .slot8 (pairFst z)) := (get_binary P a .slot8).comp HQ
  have HX : BinaryFn (fun z => get P .slot15 (pairFst z)) := (get_binary P a .slot15).comp HQ
  have HA : BinaryFn (fun z => P.ambient (RankedHistoryTask.root (pairFst z)) + 1) :=
    ((BinaryFn.ofUnary (a.ambient.comp RankedHistoryTask.root_FP)).add (BinaryFn.const 1)).comp HQ
  exact (HI.lt HA).and (((BinaryFn.const 1).le HX).and (HX.le (BinaryFn.const 4)))

def constantBranch (P : Parameters) (z : List Bool) : Prop :=
  get P .slot15 (pairFst z) = 1 ∨
    get P .row (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z) =
      get P .col (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z)

theorem constantBranch_FP (P : Parameters) (a : Access P) : FPPred (constantBranch P) := by
  have HX : BinaryFn (fun z => get P .slot15 (pairFst z)) := (get_binary P a .slot15).comp pairFst_mem_FP
  have HR : BinaryFn (fun z => get P .row (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z)) :=
    ((get_binary P a .row).mod (IntegralMixedHeightTableQueryBits.radix_binary P a)).comp pairFst_mem_FP
  have HT : BinaryFn (fun z => get P .col (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z)) :=
    ((get_binary P a .col).mod (IntegralMixedHeightTableQueryBits.radix_binary P a)).comp pairFst_mem_FP
  exact (HX.eq (BinaryFn.const 1)).or (HR.eq HT)

def slopeBranch (P : Parameters) (z : List Bool) : Prop :=
  get P .row (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z) =
    get P .col (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z) + 1 ∧
      IntegralMixedFramedHeightAffineSumBits.diagonal P z

theorem slopeBranch_FP (P : Parameters) (a : Access P) : FPPred (slopeBranch P) := by
  have HR : BinaryFn (fun z => get P .row (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z)) :=
    ((get_binary P a .row).mod (IntegralMixedHeightTableQueryBits.radix_binary P a)).comp pairFst_mem_FP
  have HT : BinaryFn (fun z => get P .col (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z) + 1) :=
    (((get_binary P a .col).mod (IntegralMixedHeightTableQueryBits.radix_binary P a)).add (BinaryFn.const 1)).comp pairFst_mem_FP
  exact (HR.eq HT).and (IntegralMixedFramedHeightAffineSumBits.diagonal_FP P a)

noncomputable def constantValue (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  multiply P (pair z (pair (IntegralMixedFramedHeightScaleFactorBits.factor P D J z) (IntegralMixedFramedHeightAffineSumBits.value P D J z)))
noncomputable def slopeValue (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  multiply P (pair z (pair (IntegralMixedFramedHeightScaleFactorBits.factor P D J z) (IntegralMixedFramedHeightAffineSumBits.coefficient P D J 3 z)))

attribute [local irreducible] multiply IntegralMixedFramedHeightScaleFactorBits.factor
  IntegralMixedFramedHeightAffineSumBits.value IntegralMixedFramedHeightAffineSumBits.coefficient

theorem constantValue_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (constantValue P D J) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedFramedHeightScaleFactorBits.factor_space P a D J hp).pairOutputs
    (IntegralMixedFramedHeightAffineSumBits.value_space P a D J hp))).postcompose (multiply P) (multiply_FP P a)

theorem slopeValue_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) :
    SpaceFunction (slopeValue P D J) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedFramedHeightScaleFactorBits.factor_space P a D J hp).pairOutputs
    (IntegralMixedFramedHeightAffineSumBits.coefficient_space P D J hp 3))).postcompose (multiply P) (multiply_FP P a)

noncomputable def post (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) :=
  if guard P z then if constantBranch P z then constantValue P D J z else if slopeBranch P z then slopeValue P D J z else [] else []

theorem post_space (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (hp : Primitive P D J) : SpaceFunction (post P D J) := by
  have E := SpaceFunction.branch _ (guard_FP P a).flag_mem_FP
    (SpaceFunction.branch _ (constantBranch_FP P a).flag_mem_FP (constantValue_space P a D J hp)
      (SpaceFunction.branch _ (slopeBranch_FP P a).flag_mem_FP (slopeValue_space P a D J hp) (SpaceFunction.ofFP _ (constFn_mem_FP []))))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)

noncomputable def scalar (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  if guard P z then
    if constantBranch P z then IntegralMixedFramedHeightScaleFactorBits.factorScalar P D J z * IntegralMixedFramedHeightAffineSumBits.scalar P D J z
    else if slopeBranch P z then IntegralMixedFramedHeightScaleFactorBits.factorScalar P D J z * (cell P D J (pairFst z) 3 0 : ZMod (modulus P (pairFst z))) else 0
  else 0

theorem post_eq (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (z : List Bool) : post P D J z = residueBits (scalar P D J z) := by
  unfold post scalar
  split_ifs
  · rw [constantValue, IntegralMixedFramedHeightScaleFactorBits.factor_value, IntegralMixedFramedHeightAffineSumBits.value_eq, multiply_packet]
  · rw [slopeValue, IntegralMixedFramedHeightScaleFactorBits.factor_value, IntegralMixedFramedHeightAffineSumBits.coefficient_value, multiply_packet]
  all_goals exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedFramedHeightPostBits
