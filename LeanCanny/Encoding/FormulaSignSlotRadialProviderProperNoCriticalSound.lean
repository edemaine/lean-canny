/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalFields
/-! # Native no-critical acceptance excludes critical heights at the original fields

The prepared parent and child retain their own complete words. Every frozen
level and both interval endpoints are read from the original atomic full word
through the verified equality scans. This is the acceptance-to-geometry
soundness direction; reverse acceptance is not asserted here.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "K"=>FormulaSignSlotRadialProviderCriticalPrefixes.key false
local notation "Q"=>query
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def originalField (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (i : ℕ) : ℝ:=
  FormulaSignSlotRadialProviderFieldEquality.point
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) i

noncomputable def OriginalCriticalFree (q w : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) : Prop:=
  let HG:=parent_point_good q w hv hd
  Disjoint (Set.Ioo
    (originalField q hv (IntegralMixedRoadmapProper.producer false q))
    (originalField q hv (IntegralMixedRoadmapProper.producer true q)))
    (IntegralMixedFrozenFrame.realCriticalValues ((G).spatial (K (Q (pair q w))))
      (IntegralMixedFrozenFrame.line
        (IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1).frame
        ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)
      (fun i : Fin ((G).birth (K (Q (pair q w))))=>originalField q hv
        (FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q w))-1-i.val))
      ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)

theorem witness_original_critical_free (q wF wP : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (H : Witness (pair (pair q wF) wP)) : OriginalCriticalFree q wP hv hd :=by
  obtain ⟨hp,HF⟩:=witness_coarse_critical_free q wF wP hv hd H
  have HL:=witness_endpoint_field false q wF wP hv H hp
  have HR:=witness_endpoint_field true q wF wP hv H hp
  have HE : FormulaSignSlotRadialProviderCriticalInterval.parentValues
      (Q (pair q wP)) hp=(fun i : Fin ((G).birth (K (Q (pair q wP))))=>originalField q hv
        (FormulaSignSlotRadialProviderCriticalPrefixes.birth false (Q (pair q wP))-1-i.val)):=by
    funext i
    exact witness_parent_fields q wF wP hv H hp i
  simp only [Bool.false_eq_true,ite_false,ite_true] at HL HR
  unfold CoarseCriticalFree at HF
  rw [HL,HR,HE] at HF
  exact HF

theorem noCritical_original_critical_free (q : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q)
    (H : NoCritical q) : ∃wP,OriginalCriticalFree q wP hv hd :=by
  obtain ⟨wF,_,wP,_,HW⟩:=H
  exact ⟨wP,witness_original_critical_free q wF wP hv hd HW⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
