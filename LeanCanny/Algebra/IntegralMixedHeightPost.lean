/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightAffineSum
public import LeanCanny.Algebra.IntegralMixedHeightScaleFactor
/-! # Charged scalar-height postprocessing for physical and nilpotent sources -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightPostBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightCellsBits (cell Primitive)
open IntegralMixedHeightReferenceSumBits (multiply multiply_FP multiply_packet)
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
      IntegralMixedHeightAffineSumBits.diagonal P z

theorem slopeBranch_FP (P : Parameters) (a : Access P) : FPPred (slopeBranch P) := by
  have HR : BinaryFn (fun z => get P .row (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z)) :=
    ((get_binary P a .row).mod (IntegralMixedHeightTableQueryBits.radix_binary P a)).comp pairFst_mem_FP
  have HT : BinaryFn (fun z => get P .col (pairFst z) % IntegralMixedHeightTableQueryBits.radix P (pairFst z) + 1) :=
    (((get_binary P a .col).mod (IntegralMixedHeightTableQueryBits.radix_binary P a)).add (BinaryFn.const 1)).comp pairFst_mem_FP
  exact (HR.eq HT).and (IntegralMixedHeightAffineSumBits.diagonal_FP P a)

noncomputable def constantValue (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :=
  multiply P (pair z (pair (IntegralMixedHeightScaleFactorBits.factor P D z) (IntegralMixedHeightAffineSumBits.value P D z)))
noncomputable def slopeValue (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :=
  multiply P (pair z (pair (IntegralMixedHeightScaleFactorBits.factor P D z) (IntegralMixedHeightAffineSumBits.coefficient P D 3 z)))

theorem constantValue_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) :
    SpaceFunction (constantValue P D) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedHeightScaleFactorBits.factor_space P a D hp).pairOutputs
    (IntegralMixedHeightAffineSumBits.value_space P a D hp))).postcompose (multiply P) (multiply_FP P a)

theorem slopeValue_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) :
    SpaceFunction (slopeValue P D) :=
  ((SpaceFunction.ofFP _ id_mem_FP).pairOutputs ((IntegralMixedHeightScaleFactorBits.factor_space P a D hp).pairOutputs
    (IntegralMixedHeightAffineSumBits.coefficient_space P D hp 3))).postcompose (multiply P) (multiply_FP P a)

noncomputable def post (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) :=
  if guard P z then if constantBranch P z then constantValue P D z else if slopeBranch P z then slopeValue P D z else [] else []

theorem post_space (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (hp : Primitive P D) : SpaceFunction (post P D) := by
  have E := SpaceFunction.branch _ (guard_FP P a).flag_mem_FP
    (SpaceFunction.branch _ (constantBranch_FP P a).flag_mem_FP (constantValue_space P a D hp)
      (SpaceFunction.branch _ (slopeBranch_FP P a).flag_mem_FP (slopeValue_space P a D hp) (SpaceFunction.ofFP _ (constFn_mem_FP []))))
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun z => by simp only [decide_eq_true_eq]; rfl)

noncomputable def scalar (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) : ZMod (modulus P (pairFst z)) :=
  if guard P z then
    if constantBranch P z then IntegralMixedHeightScaleFactorBits.factorScalar P D z * IntegralMixedHeightAffineSumBits.scalar P D z
    else if slopeBranch P z then IntegralMixedHeightScaleFactorBits.factorScalar P D z * (cell P D (pairFst z) 3 0 : ZMod (modulus P (pairFst z))) else 0
  else 0

theorem post_eq (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (z : List Bool) : post P D z = residueBits (scalar P D z) := by
  unfold post scalar
  split_ifs
  · rw [constantValue, IntegralMixedHeightScaleFactorBits.factor_value, IntegralMixedHeightAffineSumBits.value_eq, multiply_packet]
  · rw [slopeValue, IntegralMixedHeightScaleFactorBits.factor_value, IntegralMixedHeightAffineSumBits.coefficient_value, multiply_packet]
  all_goals exact ArithmeticBits.zero_residueBits _

end LeanCanny.Algebra.IntegralMixedHeightPostBits
