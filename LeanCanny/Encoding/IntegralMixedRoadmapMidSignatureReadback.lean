/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapMidSignatureLookup
public import LeanCanny.Encoding.IntegralMixedRoadmapMidpointPoint
public import LeanCanny.Encoding.IntegralMixedRoadmapEdge
/-! # Matching accepted midpoint signatures identify the entire physical point -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalFieldEquality.point
 IntegralMixedRoadmapAtomic.Valid midpointPoint

noncomputable def signatureValue (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (i : ℕ):=
  IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
    (Nat.fromBitsLE (WordList.get (ownSignature hn ht ha hR0 q) i))

theorem point_signature (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (HM : Midpoint hn ht ha hR0 q) (i : Fin (D q+1)) :
    midpointPoint hn ht ha hR0 q hv i=if i.val=levelIndex q then
      (signatureValue hn ht ha hR0 q hv (levelIndex q)+signatureValue hn ht ha hR0 q hv (D q+1))/2
      else signatureValue hn ht ha hR0 q hv i.val :=by
  have HB:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  have HK : levelIndex q ≤ D q:=by unfold levelIndex;omega
  by_cases HI : i.val=levelIndex q
  · rw [ite_eq_left HI,midpointPoint_height hn ht ha hR0 q hv hd HM i HI]
    unfold signatureValue ownSignature
    rw [signature_lookup_left _ _ _ HK,signature_lookup_right]
  · rw [ite_eq_right HI]
    by_cases HL : i.val < levelIndex q
    · rw [midpointPoint_frozen hn ht ha hR0 q hv hd HM i HL]
      unfold signatureValue ownSignature
      rw [signature_lookup_frozen _ _ _ _ HL HK]
    · have HG : levelIndex q < i.val:=by omega
      rw [midpointPoint_free hn ht ha hR0 q hv hd HM i HG]
      unfold signatureValue ownSignature
      rw [signature_lookup_free _ _ _ _ HG (by omega)]

private theorem fin_heq_iff {a b : ℕ} (H : a=b) (p : Fin a→ℝ) (q : Fin b→ℝ) :
    HEq p q↔∀i,p i=q (Fin.cast H i) :=by
  cases H
  constructor
  · intro HE i
    exact congrFun (eq_of_heq HE) i
  · intro HE
    exact heq_of_eq (funext HE)

attribute [local irreducible] signatureValue

theorem language_midpoint_eq (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (MA : Midpoint hn ht ha hR0 a) (MB : Midpoint hn ht ha hR0 b)
    (H : pair a b∈language hn ht ha hR0) :
    HEq (midpointPoint hn ht ha hR0 a hA) (midpointPoint hn ht ha hR0 b hB) :=by
  have HC : D a=D b∧IntegralMixedRoadmapAtomic.depth a=IntegralMixedRoadmapAtomic.depth b∧
      0<IntegralMixedRoadmapAtomic.depth a:=by
    simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using H.1
  have HK : levelIndex a=levelIndex b:=congrArg (fun k : ℕ=>k-1) HC.2.1
  have HA : 0<IntegralMixedRoadmapAtomic.depth a:=HC.2.2
  have HB : 0<IntegralMixedRoadmapAtomic.depth b:=HC.2.1 ▸ HA
  have HV (j : ℕ) (hj : j < D a+2) :
      signatureValue hn ht ha hR0 a hA j=signatureValue hn ht ha hR0 b hB j:=by
    simpa only [signatureValue] using language_values hn ht ha hR0 a b hA hB H j hj
  apply (fin_heq_iff (congrArg (·+1) HC.1) _ _).mpr
  intro i
  rw [point_signature hn ht ha hR0 a hA HA MA i,
    point_signature hn ht ha hR0 b hB HB MB (Fin.cast (congrArg (·+1) HC.1) i)]
  simp only [Fin.val_cast,←HK,←HC.1]
  by_cases HI : i.val=levelIndex a
  · rw [ite_eq_left HI,ite_eq_left HI,HV (levelIndex a) (by rw [←HI];omega),HV (D a+1) (by omega)]
  · rw [ite_eq_right HI,ite_eq_right HI,HV i.val (by omega)]


theorem proper_midpoint_eq (a b : List Bool) (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b)
    (H : IntegralMixedRoadmapEdge.Proper hn ht ha hR0 (pair a b)) :
    HEq (midpointPoint hn ht ha hR0 a hA) (midpointPoint hn ht ha hR0 b hB) :=by
  have HL : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 a:=by
    simpa only [pairFst_pair] using H.2.1
  have HR : IntegralMixedRoadmapLocalEdge.Local hn ht ha hR0 b:=by
    simpa only [pairSnd_pair] using H.2.2.1
  exact language_midpoint_eq hn ht ha hR0 a b hA hB HL.2.1.2.2.1 HR.2.1.2.2.1 H.2.2.2

end LeanCanny.Encoding.IntegralMixedRoadmapProperMidSignature
