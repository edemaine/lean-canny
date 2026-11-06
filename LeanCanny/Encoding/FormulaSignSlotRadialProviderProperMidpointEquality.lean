/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignatureValues
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointCoordinates
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
/-! # Matching actual native midpoint signatures identify the entire MID anchor -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
open LeanCanny.Algebra LeanCanny.Computation
open IntegralMixedRoadmapProper FormulaSignSlotRadialProviderProperLocalFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderAtomic.dimension IntegralMixedFramedHistoryFamilyBits.family
  FormulaSignSlotRadialProviderProperLocalFrame.midpoint FormulaSignSlotRadialProviderProperLocalFrame.ambient signatureValue

private theorem signature_plain (n initial : ℕ) (q : List Bool) :
    signature n initial q=IntegralMixedRoadmapProperMidSignature.signature n initial q := rfl

theorem point_signature (q : List Bool) (hv : A q) (HB : FormulaSignSlotRadialProviderProper.Base q)
    (i : Fin (ambient q+1)) :
    midpoint q hv i=if i.val=levelIndex q then
      (signatureValue q hv (levelIndex q)+signatureValue q hv (D q+1))/2 else signatureValue q hv i.val := by
  have HD := FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HP : 0<FormulaSignSlotRadialProviderAtomic.depth q := HB.1
  have HK : levelIndex q≤D q := by
    unfold levelIndex
    change FormulaSignSlotRadialProviderAtomic.depth q-1≤D q
    omega
  by_cases HI : i.val=levelIndex q
  · rw [ite_eq_left HI,midpoint_height q hv HB i HI]
    unfold signatureValue ownSignature
    rw [signature_plain,IntegralMixedRoadmapProperMidSignature.signature_lookup_left _ _ _ HK,
      IntegralMixedRoadmapProperMidSignature.signature_lookup_right]
    rfl
  · rw [ite_eq_right HI]
    by_cases HL : i.val<levelIndex q
    · rw [midpoint_frozen q hv HB i HL]
      unfold signatureValue ownSignature
      rw [signature_plain,IntegralMixedRoadmapProperMidSignature.signature_lookup_frozen _ _ _ _ HL HK]
      rfl
    · have HG : levelIndex q< i.val := by omega
      have HN : i.val≤D q := by have H := i.isLt;have HA := ambient_eq q;omega
      have HF : FormulaSignSlotRadialProviderAtomic.depth q≤ i.val := by
        unfold levelIndex at HG
        change FormulaSignSlotRadialProviderAtomic.depth q-1< i.val at HG
        omega
      rw [midpoint_free q hv HB i HF]
      unfold signatureValue ownSignature
      rw [signature_plain,IntegralMixedRoadmapProperMidSignature.signature_lookup_free _ _ _ _ HG HN]
      rfl

private theorem reconstructed_points_heq {n m : ℕ} (hd : n=m)
    (k l lastA lastB bound : ℕ) (hk : k=l) (hl : lastA=lastB)
    (v w : ℕ→ℝ) (hn : n≤bound) (hLast : lastA<bound)
    (hv : ∀j,j<bound→v j=w j) (p : Fin n→ℝ) (q : Fin m→ℝ)
    (hp : ∀i,p i=if i.val=k then (v k+v lastA)/2 else v i.val)
    (hq : ∀i,q i=if i.val=l then (w l+w lastB)/2 else w i.val) : HEq p q := by
  cases hd
  cases hk
  cases hl
  apply heq_of_eq
  funext i
  rw [hp i,hq i]
  have hi : i.val<bound := i.isLt.trans_le hn
  by_cases H : i.val=k
  · rw [ite_eq_left H,ite_eq_left H,hv k (H ▸ hi),hv lastA hLast]
  · rw [ite_eq_right H,ite_eq_right H,hv i.val hi]

theorem language_midpoint_eq (a b : List Bool) (ha : A a) (hb : A b)
    (BA : FormulaSignSlotRadialProviderProper.Base a) (BB : FormulaSignSlotRadialProviderProper.Base b)
    (H : pair a b∈language) : HEq (midpoint a ha) (midpoint b hb) := by
  have HC : D a=D b ∧ FormulaSignSlotRadialProviderAtomic.depth a=FormulaSignSlotRadialProviderAtomic.depth b ∧
      0<FormulaSignSlotRadialProviderAtomic.depth a := by
    simpa only [Compatible,left,right,pairFst_pair,pairSnd_pair] using H.1
  have HK : levelIndex a=levelIndex b := congrArg (fun k : ℕ=>k-1) HC.2.1
  have HD : ambient a=ambient b := (ambient_eq a).trans (HC.1.trans (ambient_eq b).symm)
  apply reconstructed_points_heq (congrArg (·+1) HD) (levelIndex a) (levelIndex b)
    (D a+1) (D b+1) (D a+2) HK (congrArg (·+1) HC.1)
    (signatureValue a ha) (signatureValue b hb)
    (by have HA := ambient_eq a;omega) (by omega)
    (fun j hj=>language_values a b ha hb H j hj) (midpoint a ha) (midpoint b hb)
    (fun i=>point_signature a ha BA i) (fun i=>point_signature b hb BB i)

theorem proper_midpoint_eq (a b : List Bool) (ha : A a) (hb : A b)
    (H : FormulaSignSlotRadialProviderEdge.Proper (pair a b)) : HEq (midpoint a ha) (midpoint b hb) := by
  have HA : FormulaSignSlotRadialProviderLocalEdge.Local a := by simpa only [pairFst_pair] using H.2.1
  have HB : FormulaSignSlotRadialProviderLocalEdge.Local b := by simpa only [pairSnd_pair] using H.2.2.1
  exact language_midpoint_eq a b ha hb HA.2.1 HB.2.1 H.2.2.2

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
