/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
/-! # The actual marked and outer factories leave a strict scalar padding margin -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutStrictMargin
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedFramedHistoryFamilyBits (family)
set_option backward.isDefEq.respectTransparency false

theorem source_cap_lt (ambient degree bound count : List Bool→ℕ) (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap (ambient root+1) (degree root)<
      2^(IntegralMixedSourceIntegerPrelude.parameters ambient degree bound count).width root:=
 (Nat.le_add_right _ _).trans_lt (Nat.lt_size_self _)

variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedSourceIntegerPrelude.ceiling IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedAuxiliaryMarkedIntegerSource.number

theorem actual_cap_lt (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((bank hn ht ha hR outer).parameters.ambient root+1)
      ((bank hn ht ha hR outer).parameters.degree root)<2^(bank hn ht ha hR outer).parameters.width root:=by
 cases outer <;>
   simp only [bank,Bool.false_eq_true,ite_false,ite_true,
     IntegralMixedAuxiliaryMarkedRecordPlan.bank,IntegralMixedAuxiliaryOuterRecordPlan.bank,
     IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters,IntegralMixedAuxiliaryOuterRecordPlan.certifiedParameters,
     IntegralMixedFramedNormalizationBits.planned,IntegralMixedAuxiliaryMarkedRecordPlan.parameters,
     IntegralMixedAuxiliaryOuterRecordPlan.parameters,IntegralMixedSourceIntegerPrelude.parameters]
 all_goals
   exact source_cap_lt (fun c=>IntegralMixedAuxiliaryMarkedIntegerSource.number n c+3)
     (IntegralMixedAuxiliaryMarkedIntegerPlan.degree t)
     (IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha) (fun _=>0) root

attribute [local irreducible] bank

theorem selected_degree_lt (key : List Bool) :
    (family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).degree key<2^(bank hn ht ha hR outer).parameters.width (pairFst key):=by
 have H:=(family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).degree_bound key
 have HE:=(bank hn ht ha hR outer).data.degree_eq key
 change (family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
      (bank hn ht ha hR outer).data).degree key≤IntegralMixedExceptionalBounds.auxiliaryCap
        ((bank hn ht ha hR outer).parameters.ambient (pairFst key)+1)
        (IntegralMixedFramedHistoryFamilyBits.instruction (bank hn ht ha hR outer).parameters
          (bank hn ht ha hR outer).plan key).source.degree at H
 rw [HE] at H
 exact H.trans_lt (actual_cap_lt hn ht ha hR outer _)

end LeanCanny.Encoding.IntegralMixedPhysicalCutStrictMargin
