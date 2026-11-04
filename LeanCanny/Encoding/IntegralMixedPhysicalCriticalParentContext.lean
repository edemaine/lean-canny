/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixPoint
/-! # A critical probe's parent word is allocated before its auxiliary context -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalParentContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family keyAt)
open IntegralMixedPhysicalCriticalPrefixes (input key positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B

private theorem input_keys (PP : Parameters) (DD : IntegralMixedFramedHistoryFamilyBits.Plan PP)
    (HH : IntegralMixedFramedHistoryFamilyBits.Data PP DD) (LL FF CC : List Bool→ℕ)
    (hss : IntegralMixedFramedStepHeight.FamilyInputs PP DD LL FF CC) (k l : List Bool→List Bool)
    (hk : ∀q,0<(family PP DD HH).birth (k q)) (hl : ∀q,0<(family PP DD HH).birth (l q)) (he : k=l) :
    IntegralFramedPhysicalSquare.input PP DD HH LL FF CC hss k hk=
      IntegralFramedPhysicalSquare.input PP DD HH LL FF CC hss l hl :=by
  subst l
  rfl

theorem root_positive (r : List Bool) :
    0<(family P D H).birth (keyAt r (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r-1) []) :=by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,
    IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P r _ [] (by
      change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r-1≤
        IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r+2+1
      omega)]
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  omega

noncomputable def rootInput:=IntegralFramedPhysicalSquareContext.rootInput P D H L F C hs
  (fun r=>IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r-1) (root_positive hn ht ha hR)

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem input_factor : input hn ht ha hR false false=
    SquareSampleInput.comp (rootInput hn ht ha hR) pairFst :=by
  have HK : key n false false=(fun q=>keyAt (pairFst q)
      (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q)-1) q):=by
    funext q
    simp only [key,IntegralMixedPhysicalCriticalPrefixes.birth,
      IntegralMixedPhysicalMarkedPlan.leafCount,IntegralMixedPhysicalCriticalQuery.root,
      pairFst_pair,Bool.false_eq_true,ite_false,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  have HE:=input_keys P D H L F C hs (key n false false) _ (positive hn ht ha hR false false)
    (fun q=>IntegralFramedPhysicalSquareContext.positive_aux P D H (pairFst q)
      (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q)-1) [] q
      (root_positive hn ht ha hR (pairFst q))) HK
  exact HE.trans (IntegralFramedPhysicalSquareContext.input_root_factor P D H L F C hs
    (fun r=>IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r-1) id (root_positive hn ht ha hR))

theorem valid_root (q w : List Bool) :
    SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q w↔
      SquareSampleCompleteVertices.Valid (rootInput hn ht ha hR) (pairFst q) w :=by
  rw [input_factor]
  exact SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _

theorem valid_iff (q r w : List Bool) (he : pairFst q=pairFst r) :
    SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q w↔
      SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) r w :=by
  rw [valid_root,valid_root,he]

theorem width_eq (q r : List Bool) (he : pairFst q=pairFst r) :
    SquareSampleCompleteVertices.width (input hn ht ha hR false false) q=
      SquareSampleCompleteVertices.width (input hn ht ha hR false false) r :=by
  rw [input_factor,SquareSampleCompleteNaturality.complete_width_comp,
    SquareSampleCompleteNaturality.complete_width_comp,he]

private theorem natural_input_eq (I J : SquareSampleInput.Inputs) (he : I=J) (q w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid I q w) (hj : SquareSampleCompleteVertices.Valid J q w) :
    IntegralFramedPhysicalSquareContext.naturalValue I q w hi=
      IntegralFramedPhysicalSquareContext.naturalValue J q w hj :=by cases he;rfl

private theorem natural_comp (I : SquareSampleInput.Inputs) (f : List Bool→List Bool) (q w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp I f) q w)
    (hj : SquareSampleCompleteVertices.Valid I (f q) w) :
    IntegralFramedPhysicalSquareContext.naturalValue (SquareSampleInput.comp I f) q w hi=
      IntegralFramedPhysicalSquareContext.naturalValue I (f q) w hj :=by
  funext i
  unfold IntegralFramedPhysicalSquareContext.naturalValue
  change (if h : i<I.count (f q) then
    (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp I f) q w hi).val ⟨i,h⟩ else 0)=_
  split_ifs with h
  · exact congrFun (SquareSampleCompleteNaturality.candidate_comp I f q w hi hj) ⟨i,h⟩
  · rfl

private theorem natural_context (I : SquareSampleInput.Inputs) (q r w : List Bool) (he : q=r)
    (hq : SquareSampleCompleteVertices.Valid I q w) (hr : SquareSampleCompleteVertices.Valid I r w) :
    IntegralFramedPhysicalSquareContext.naturalValue I q w hq=
      IntegralFramedPhysicalSquareContext.naturalValue I r w hr :=by subst r;rfl

theorem natural_root (q w : List Bool)
    (hq : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q w) :
    IntegralFramedPhysicalSquareContext.naturalValue (input hn ht ha hR false false) q w hq=
      IntegralFramedPhysicalSquareContext.naturalValue (rootInput hn ht ha hR) (pairFst q) w
        ((valid_root hn ht ha hR q w).mp hq) :=by
  have HI:=input_factor hn ht ha hR
  have HC : SquareSampleCompleteVertices.Valid
      (SquareSampleInput.comp (rootInput hn ht ha hR) pairFst) q w:=HI ▸ hq
  exact (natural_input_eq _ _ HI q w hq HC).trans (natural_comp _ _ q w HC _)

theorem natural_eq (q r w : List Bool) (he : pairFst q=pairFst r)
    (hq : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q w)
    (hr : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) r w) :
    IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (key n false false)
      (positive hn ht ha hR false false) q w hq=
    IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (key n false false)
      (positive hn ht ha hR false false) r w hr :=by
  change IntegralFramedPhysicalSquareContext.naturalValue (input hn ht ha hR false false) q w hq=
    IntegralFramedPhysicalSquareContext.naturalValue (input hn ht ha hR false false) r w hr
  rw [natural_root hn ht ha hR q w hq,natural_root hn ht ha hR r w hr]
  exact natural_context _ _ _ w he _ _

private noncomputable def observationAt (PP : Parameters) (DD : IntegralMixedFramedHistoryFamilyBits.Plan PP)
    (k : IntegralMixedFramedCompanionBits.PrefixKey PP) :=
  IntegralMixedFramedRunObservation.ofCommands (IntegralMixedFramedHistoryFamilyBits.initial PP DD k.root)
    (IntegralMixedFramedHistoryScript.paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction PP DD k.root)
      (DD.rules k.root) k.birth)
    (by rw [IntegralMixedFramedHistoryScript.paddedPast_length];exact k.bounded.trans (Nat.le_succ _))

theorem point_eq (q r w : List Bool) (he : pairFst q=pairFst r)
    (hq : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) q w)
    (hr : SquareSampleCompleteVertices.Valid (input hn ht ha hR false false) r w)
    (i : Fin ((family P D H).birth (key n false false q)))
    (j : Fin ((family P D H).birth (key n false false r))) (hij : i.val=j.val) :
    IntegralFramedPhysicalSquare.point P D H L F C hs (key n false false)
      (positive hn ht ha hR false false) q w hq i=
    IntegralFramedPhysicalSquare.point P D H L F C hs (key n false false)
      (positive hn ht ha hR false false) r w hr j :=by
  have HB : IntegralMixedPhysicalCriticalPrefixes.birth n false false q=
      IntegralMixedPhysicalCriticalPrefixes.birth n false false r:=by
    simp only [IntegralMixedPhysicalCriticalPrefixes.birth,IntegralMixedPhysicalCriticalQuery.root,he]
  have HK : IntegralMixedFramedCompanionBits.profile P (key n false false q)=
      IntegralMixedFramedCompanionBits.profile P (key n false false r):=by
    apply IntegralMixedFramedCompanionBits.PrefixKey.ext
    · simpa only [IntegralMixedFramedCompanionBits.profile,key,
        IntegralMixedFramedHistoryFamilyBits.keyAt,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair] using he
    · exact (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).symm.trans
        ((IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false false q).trans
          (HB.trans ((IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR false false r).symm.trans
            (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _))))
  have HO:=congrArg (observationAt P D) HK
  have HN:=natural_eq hn ht ha hR q r w he hq hr
  have Hq:=IntegralFramedPhysicalPrefixPoint.full_point P D H L F C hs (key n false false)
    (positive hn ht ha hR false false) q w hq i
  have Hr:=IntegralFramedPhysicalPrefixPoint.full_point P D H L F C hs (key n false false)
    (positive hn ht ha hR false false) r w hr j
  have HE:=congrArg₂ (fun O z=>O.point z i.val) HO HN
  exact Hq.symm.trans (HE.trans (hij ▸ Hr))

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalParentContext
