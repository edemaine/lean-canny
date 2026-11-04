/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalFields
/-! # Native no-critical acceptance excludes critical heights at the original fields

The prepared parent and child retain their own complete words. Every frozen
level and both interval endpoints are read from the original atomic full word
through the verified equality scans. This is the acceptance-to-geometry
soundness direction; reverse acceptance is not asserted here.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family (IntegralFramedBankQuery.Bank.parameters B)
  (IntegralFramedBankQuery.Bank.plan B) (IntegralFramedBankQuery.Bank.data B)
local notation "K"=>IntegralMixedPhysicalCriticalPrefixes.key n false false
local notation "Q"=>query hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

noncomputable def originalField (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (i : ℕ) : ℝ:=
  IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) i

noncomputable def OriginalCriticalFree (q w : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q) : Prop:=
  let HG:=parent_point_good hn ht ha hR0 q w hv hd
  Disjoint (Set.Ioo
    (originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
    (originalField hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)))
    (IntegralMixedFrozenFrame.realCriticalValues ((G).spatial (K (Q (pair q w))))
      (IntegralMixedFrozenFrame.line
        (IntegralMixedChronologicalFrameCode.descriptor _ _ (IntegralMixedRoadmapProper.labels q) HG.1).frame
        ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)
      (fun i : Fin ((G).birth (K (Q (pair q w))))=>originalField hn ht ha hR0 q hv
        (IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q w))-1-i.val))
      ⟨IntegralMixedRoadmapProper.levelIndex q,HG.2.2.1⟩)

theorem witness_original_critical_free (q wF wP : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (H : Witness hn ht ha hR0 (pair (pair q wF) wP)) : OriginalCriticalFree hn ht ha hR0 q wP hv hd :=by
  obtain ⟨hp,HF⟩:=witness_coarse_critical_free hn ht ha hR0 q wF wP hv hd H
  have HL:=witness_endpoint_field hn ht ha hR0 false q wF wP hv H hp
  have HR:=witness_endpoint_field hn ht ha hR0 true q wF wP hv H hp
  have HE : IntegralMixedPhysicalCriticalInterval.parentValues hn ht ha (radius_binary hR0) false
      (Q (pair q wP)) hp=(fun i : Fin ((G).birth (K (Q (pair q wP))))=>originalField hn ht ha hR0 q hv
        (IntegralMixedPhysicalCriticalPrefixes.birth n false false (Q (pair q wP))-1-i.val)):=by
    funext i
    exact witness_parent_fields hn ht ha hR0 q wF wP hv H hp i
  simp only [Bool.false_eq_true,ite_false,ite_true] at HL HR
  unfold CoarseCriticalFree at HF
  rw [HL,HR,HE] at HF
  exact HF

theorem noCritical_original_critical_free (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (hd : 0<IntegralMixedRoadmapAtomic.depth q)
    (H : NoCritical hn ht ha hR0 q) : ∃wP,OriginalCriticalFree hn ht ha hR0 q wP hv hd :=by
  obtain ⟨wF,_,wP,_,HW⟩:=H
  exact ⟨wP,witness_original_critical_free hn ht ha hR0 q wF wP hv hd HW⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
