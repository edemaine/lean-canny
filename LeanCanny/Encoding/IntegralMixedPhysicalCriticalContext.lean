/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankObservations
public import LeanCanny.Algebra.IntegralMixedFullBankObservationOrigin
/-! # The completed critical child has the actual marked full tuple at its root -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family keyAt prefixLength)
open IntegralMixedPhysicalCriticalPrefixes (key input positive birth)
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
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

def context (q : List Bool):=pair (IntegralMixedPhysicalCriticalQuery.root q) []

theorem full_birth (q : List Bool) : birth n false true q=
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q) :=by
  simp only [IntegralMixedPhysicalCriticalPrefixes.birth,IntegralMixedPhysicalMarkedPlan.leafCount,pairFst_pair,
    Bool.false_eq_true,ite_false,ite_true,Nat.sub_zero,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,
    IntegralMixedPhysicalCriticalQuery.root]

theorem full_key : key n false true=(fun q=>keyAt (pairFst q)
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q)) q) :=by
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

theorem input_factor : input hn ht ha hR false true=SquareSampleInput.comp
    (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR) pairFst :=by
  have HE:=input_keys P D H L F C hs (key n false true) _ (positive hn ht ha hR false true)
    (fun q=>IntegralFramedPhysicalSquareContext.positive_aux P D H (pairFst q)
      (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n (pairFst q)) [] q
      (IntegralMixedPhysicalMarkedContext.root_positive hn ht ha hR (pairFst q))) (full_key (n:=n))
  exact HE.trans (IntegralFramedPhysicalSquareContext.input_root_factor P D H L F C hs
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n) id
    (IntegralMixedPhysicalMarkedContext.root_positive hn ht ha hR))

theorem valid_full (q w : List Bool) :
    SquareSampleCompleteVertices.Valid (input hn ht ha hR false true) q w ↔
      SquareSampleCompleteVertices.Valid S (context q) w :=by
  rw [input_factor,IntegralMixedPhysicalMarkedContext.input_factor]
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
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR false true) q w)
    (hc : SquareSampleCompleteVertices.Valid S (context q) w) :
    IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (key n false true)
      (positive hn ht ha hR false true) q w hv=
      IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs (B).key (B).positive (context q) w hc :=by
  have HI:=input_factor hn ht ha hR
  have hI : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp
      (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR) pairFst) q w:=HI ▸ hv
  have HR : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR)
      (pairFst q) w:=(SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _).mp hI
  have HN:=(natural_input_eq _ _ HI q w hv hI).trans (natural_comp _ _ q w hI HR)
  have HM:=IntegralMixedPhysicalMarkedContext.natural_root hn ht ha hR (context q) w hc
  have HE : IntegralFramedPhysicalSquareContext.naturalValue
      (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR) (pairFst q) w HR=
      IntegralFramedPhysicalSquareContext.naturalValue
        (IntegralMixedPhysicalMarkedContext.rootInput hn ht ha hR) (pairFst (context q)) w
        ((IntegralMixedPhysicalMarkedContext.valid_root hn ht ha hR (context q) w).mp hc):=by
    exact natural_context_congr _ _ _ w
      (by simp only [context,IntegralMixedPhysicalCriticalQuery.root,pairFst_pair]) _ _
  exact HN.trans (HE.trans HM.symm)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalContext
