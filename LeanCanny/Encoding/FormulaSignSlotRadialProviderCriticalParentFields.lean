/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBankContext
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankObservations
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalLanguageCorrectness
public import LeanCanny.Algebra.IntegralMixedFullBankObservationOrigin
/-! # Actual prepared parent values are full-child chronological fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family keyAt prefixLength)
open FormulaSignSlotRadialProviderCriticalPrefixes (key input positive birth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>family P D H
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

def context (q : List Bool):=pair (IntegralMixedPhysicalCriticalQuery.root q) []

theorem full_birth (q : List Bool) : birth true q=
    FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q) :=by
  simp only [FormulaSignSlotRadialProviderCriticalPrefixes.birth,ite_true,Nat.sub_zero,
    IntegralMixedPhysicalCriticalQuery.root]

theorem full_key : key true=(fun q=>keyAt (pairFst q)
    (FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)) q) :=by
  funext q
  rw [key,full_birth]
  rfl

private theorem input_keys (PP : Parameters) (DD : IntegralMixedFramedHistoryFamilyBits.Plan PP)
    (HH : IntegralMixedFramedHistoryFamilyBits.Data PP DD) (LL FF CC : List Bool→ℕ)
    (hss : IntegralMixedFramedStepHeight.FamilyInputs PP DD LL FF CC) (k l : List Bool→List Bool)
    (hk : ∀q,0<(family PP DD HH).birth (k q)) (hl : ∀q,0<(family PP DD HH).birth (l q)) (he : k=l) :
    IntegralFramedPhysicalSquare.input PP DD HH LL FF CC hss k hk=
      IntegralFramedPhysicalSquare.input PP DD HH LL FF CC hss l hl :=by
  subst l
  rfl

theorem input_factor : input true=SquareSampleInput.comp
    (FormulaSignSlotRadialProviderBankContext.rootInput) pairFst :=by
  have HE:=input_keys P D H L F C hs (key true) _ (positive true)
    (fun q=>IntegralFramedPhysicalSquareContext.positive_aux P D H (pairFst q)
      (FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)) [] q
      (FormulaSignSlotRadialProviderBankContext.root_positive (pairFst q))) (full_key)
  exact HE.trans (IntegralFramedPhysicalSquareContext.input_root_factor P D H L F C hs
    (FormulaSignSlotRadialProviderRecordPlan.fullCount) id
    (FormulaSignSlotRadialProviderBankContext.root_positive))

theorem valid_full (q w : List Bool) :
    SquareSampleCompleteVertices.Valid (input true) q w ↔
      SquareSampleCompleteVertices.Valid S (context q) w :=by
  rw [input_factor,FormulaSignSlotRadialProviderBankContext.input_factor]
  rw [SquareSampleCompleteNaturality.complete_valid_comp,SquareSampleCompleteNaturality.complete_valid_comp]
  simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]

private theorem natural_input_eq (I J : SquareSampleInput.Inputs) (he : I=J) (q w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid I q w) (hj : SquareSampleCompleteVertices.Valid J q w) :
    IntegralFramedPhysicalSquareContext.naturalValue I q w hi=
      IntegralFramedPhysicalSquareContext.naturalValue J q w hj :=by
  cases he
  rfl

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

private theorem natural_context_congr (I : SquareSampleInput.Inputs) (a b w : List Bool)
    (he : a=b) (ha : SquareSampleCompleteVertices.Valid I a w) (hb : SquareSampleCompleteVertices.Valid I b w) :
    IntegralFramedPhysicalSquareContext.naturalValue I a w ha=
      IntegralFramedPhysicalSquareContext.naturalValue I b w hb :=by
  subst b
  rfl

theorem natural_full (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w) :
    IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (key true)
      (positive true) q w hv=
      IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (B).key (B).positive (context q) w hc :=by
  have HI:=input_factor
  have hI : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp
      (FormulaSignSlotRadialProviderBankContext.rootInput) pairFst) q w:=HI ▸ hv
  have HR : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderBankContext.rootInput)
      (pairFst q) w:=(SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _).mp hI
  have HN:=(natural_input_eq _ _ HI q w hv hI).trans (natural_comp _ _ q w hI HR)
  have HM:=FormulaSignSlotRadialProviderBankContext.natural_root (context q) w hc
  have HE : IntegralFramedPhysicalSquareContext.naturalValue
      (FormulaSignSlotRadialProviderBankContext.rootInput) (pairFst q) w HR=
      IntegralFramedPhysicalSquareContext.naturalValue
        (FormulaSignSlotRadialProviderBankContext.rootInput) (pairFst (context q)) w
        ((FormulaSignSlotRadialProviderBankContext.valid_root (context q) w).mp hc):=by
    exact natural_context_congr _ _ _ w
      (by simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]) _ _
  exact HN.trans (HE.trans HM.symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalContext

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open FormulaSignSlotRadialProviderCriticalPrefixes (key input positive birth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>family P D H
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

theorem child_point_field (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (i : ℕ) (hi : i<birth false q) :
    FormulaSignSlotRadialProviderCriticalBankEquality.point true q w hv i=
      FormulaSignSlotRadialProviderFieldEquality.pointNewest (context q) w hc (i+1) :=by
  let z:=IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs
    (key true) (positive true) q w hv
  have HN:=natural_full q w hv hc
  have HR : pairFst (key true q)=pairFst ((B).key (context q)):=by
    rw [FormulaSignSlotRadialProviderFieldEquality.key_root]
    simp only [key,IntegralMixedFramedHistoryFamilyBits.keyAt,context,pairFst_pair]
  have HB : prefixLength P (key true q)=prefixLength P ((B).key (context q)):=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,
      ←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,
      FormulaSignSlotRadialProviderCriticalPrefixes.key_birth true]
    change birth true q=FormulaSignSlotRadialProviderFieldEquality.count (context q)
    rw [full_birth,FormulaSignSlotRadialProviderFieldEquality.count_eq]
    simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
  have HO:=IntegralMixedFullBankObservation.point_sibling P D H H (key true q)
    ((B).key (context q)) HR HB z (i+1)
  have HP:=FormulaSignSlotRadialProviderCriticalInterval.bank_point_observation true q w hv z
    (fun j=>(IntegralFramedPhysicalSquare.naturalPoint_at P D H L F C hs
      (key true) (positive true) q w hv j).symm) i hi
  have HC : i+1<FormulaSignSlotRadialProviderFieldEquality.count (context q):=by
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
    have HF:=full_birth q
    have HS:=FormulaSignSlotRadialProviderCriticalPrefixes.consecutive q
    simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
    omega
  have HE:=IntegralFramedPhysicalSquare.bank_naturalPoint P D H L F C hs (B).key (B).positive
    (context q) w hc ⟨i+1,HC⟩
  have HX : FormulaSignSlotRadialProviderFieldEquality.pointNewest (context q) w hc (i+1)=
      IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context q) w hc ⟨i+1,HC⟩:=by
    unfold FormulaSignSlotRadialProviderFieldEquality.pointNewest
    apply congrArg (IntegralFramedPhysicalSquare.point P D H L F C hs (B).key (B).positive (context q) w hc)
    apply Fin.ext
    exact min_eq_left (by omega)
  exact HP.trans (HO.trans ((congrArg (fun v=>
    (IntegralMixedFullBankObservation.atFamily P D H ((B).key (context q))).point v (i+1)) HN).trans
      (HE.trans HX.symm)))

theorem parent_point_field (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (hg : FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q w))
    (i : ℕ) (hi : i<birth false q) :
    FormulaSignSlotRadialProviderCriticalBankEquality.point false q
      (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i=
      FormulaSignSlotRadialProviderFieldEquality.pointNewest (context q) w hc (i+1) :=
  ((FormulaSignSlotRadialProviderCriticalBankEquality.agrees_iff q w hp hv).mp hg i hi).trans
    (child_point_field q w hv hc i hi)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalContext

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open FormulaSignSlotRadialProviderCriticalPrefixes (key input positive birth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>family P D H
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

theorem parentValues_point (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (i : Fin ((G).birth (key false q))) :
    FormulaSignSlotRadialProviderCriticalInterval.parentValues q hp i=
      FormulaSignSlotRadialProviderCriticalBankEquality.point false q
        (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i.val :=by
  have hi : i.val<birth false q:=i.isLt.trans_eq
    (FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false q)
  unfold FormulaSignSlotRadialProviderCriticalInterval.parentValues FormulaSignSlotRadialProviderCriticalInterval.parentArray
  rw [IntegralFramedPhysicalSquare.bank_naturalPoint]
  unfold FormulaSignSlotRadialProviderCriticalBankEquality.point
  apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
    (key false) (positive false) q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
  apply Fin.ext
  symm
  simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using
    FormulaSignSlotRadialProviderCriticalBankEquality.coordinate_val false q i.val 0 hi

theorem parentValues_field (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (hg : FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q w))
    (i : Fin ((G).birth (key false q))) :
    FormulaSignSlotRadialProviderCriticalInterval.parentValues q hp i=
      FormulaSignSlotRadialProviderFieldEquality.point (context q) w hc
        (birth false q-1-i.val) :=by
  have hi : i.val<birth false q:=i.isLt.trans_eq
    (FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false q)
  have HE:=parent_point_field q w hp hv hc hg i.val hi
  have HC : FormulaSignSlotRadialProviderFieldEquality.count (context q)=birth false q+1:=by
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
    have HF:=full_birth q
    have HS:=FormulaSignSlotRadialProviderCriticalPrefixes.consecutive q
    simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]
    omega
  have HX : FormulaSignSlotRadialProviderFieldEquality.newest
      (FormulaSignSlotRadialProviderFieldEquality.count (context q)) (birth false q-1-i.val)=i.val+1:=by
    rw [HC]
    unfold FormulaSignSlotRadialProviderFieldEquality.newest
    rw [min_eq_left (by omega : birth false q-1-i.val≤birth false q+1-1)]
    omega
  exact (parentValues_point q hp i).trans
    (HE.trans (by rw [FormulaSignSlotRadialProviderFieldEquality.point,HX]))

theorem endpoint_field (q w : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (hv : SquareSampleCompleteVertices.Valid (input true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w)
    (hg : FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q w))
    (j : ℕ) (hj : j<birth false q) :
    FormulaSignSlotRadialProviderCriticalInterval.endpointValue q hp j=
      FormulaSignSlotRadialProviderFieldEquality.point (context q) w hc j :=by
  have hi : birth false q-1-j<(G).birth (key false q):=by
    rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false]
    omega
  have HE:=parentValues_field q w hp hv hc hg ⟨birth false q-1-j,hi⟩
  have HX : birth false q-1-(birth false q-1-j)=j:=by omega
  rw [HX] at HE
  exact (parentValues_point q hp ⟨birth false q-1-j,hi⟩).symm.trans HE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalContext
