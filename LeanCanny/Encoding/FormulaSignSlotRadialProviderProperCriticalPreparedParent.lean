/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalPreparedPrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalParentContext
public import LeanCanny.Encoding.IntegralFramedPhysicalRealizedVertex
/-! # A fresh reserved critical-parent word retains original scalar values -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan family prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realized_congr {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (v w : ℕ→ℝ) (hv : IntegralMixedIntegerRealization.Realizes x v)
    (he : ∀i<m,v i=w i) : IntegralMixedIntegerRealization.Realizes x w :=by
  obtain ⟨y,φ,hy,hφ,hv⟩:=hv
  exact ⟨y,φ,hy,hφ,fun i=>(hv i).trans (he i.val i.isLt)⟩

private theorem family_realizes (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (k : List Bool) (z : ℕ→ℝ)
    (hz : (IntegralFramedPhysicalPrefixObservation.atRoot P D (pairFst k) (prefixLength P k)
      (min_le_right _ _)).Roots z) :
    IntegralMixedIntegerRealization.Realizes ((family P D H).state k)
      ((IntegralFramedPhysicalPrefixObservation.atRoot P D (pairFst k) (prefixLength P k)
        (min_le_right _ _)).point z) :=
  IntegralFramedPhysicalPrefixObservation.at_realizes P D (pairFst k) (prefixLength P k) _ z hz

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "L"=>IntegralFramedBankQuery.Bank.nodes B
local notation "F"=>IntegralFramedBankQuery.Bank.factor B
local notation "C"=>IntegralFramedBankQuery.Bank.seed B
local notation "hs"=>IntegralFramedBankQuery.Bank.bounds B
local notation "G"=>family P D H
local notation "K"=>FormulaSignSlotRadialProviderCriticalPrefixes.key false
local notation "O"=>FormulaSignSlotRadialProviderRecordPrefix.observation

noncomputable def oldNatural (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :=
  FormulaSignSlotRadialProviderRecordPrefix.natural (FormulaSignSlotRadialProviderAtomic.root q)
    (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv)

theorem prepared_initial (q : List Bool) : FormulaSignSlotRadialProviderRecordPlan.count (root q)=
    FormulaSignSlotRadialProviderAtomic.initial q :=by
  unfold FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderRecordPlan.count
  rw [prepared_provider,FormulaSignSlotRadialProviderAtomic.root_provider]

theorem originalBirth_eq (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    originalBirth q=FormulaSignSlotRadialProviderAtomic.initial q+preparedStart q :=by
  have HP:=count_positive q hv
  unfold originalBirth preparedStart
  omega

theorem prepared_birth (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    FormulaSignSlotRadialProviderCriticalPrefixes.birth false (canonical q)=
      FormulaSignSlotRadialProviderRecordPlan.count (root q)+preparedStart q :=by
  rw [prepared_initial]
  exact (query_birth q [] (count_positive q hv)).trans (originalBirth_eq q hv)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPrefix.observation oldNatural

private theorem canonical_observation (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    IntegralFramedPhysicalPrefixObservation.atRoot P D (pairFst (K (canonical q)))
      (prefixLength P (K (canonical q))) (min_le_right _ _)=
    O (root q) (preparedStart q) ((start_fit q).trans_eq (prepared_count q hv).symm) :=by
  have HR : pairFst (K (canonical q))=root q:=by
    simp only [FormulaSignSlotRadialProviderCriticalPrefixes.key,
      IntegralMixedFramedHistoryFamilyBits.keyAt,pairFst_pair,root,
      IntegralMixedPhysicalCriticalQuery.root]
  have HM : prefixLength P (K (canonical q))=
      FormulaSignSlotRadialProviderRecordPlan.count (root q)+preparedStart q :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).symm.trans
      ((FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false (canonical q)).trans (prepared_birth q hv))
  exact (IntegralFramedPhysicalPrefixObservation.at_congr P D _ _ _ _ _ _ HR HM).trans
    (FormulaSignSlotRadialProviderRecordPrefix.bank_observation _ _ _)

private theorem prepared_old_observation (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    O (root q) (preparedStart q) ((start_fit q).trans_eq (prepared_count q hv).symm)=
    O (FormulaSignSlotRadialProviderAtomic.root q) (preparedStart q) (start_fit q) :=
  (FormulaSignSlotRadialProviderRecordPrefix.observation_eq
    (FormulaSignSlotRadialProviderAtomic.root q) (root q)
    ((FormulaSignSlotRadialProviderAtomic.root_provider q).trans (prepared_provider q).symm)
    (prepared_count q hv).symm _ (start_fit q) (fun i hi=>(prepared_code q i hi).symm)).symm

private theorem old_point (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (i : ℕ) (hi : i<FormulaSignSlotRadialProviderAtomic.initial q+preparedStart q) :
    (O (FormulaSignSlotRadialProviderAtomic.root q) (preparedStart q) (start_fit q)).point (oldNatural q hv) i=
      originalNaturalValues q hv i :=by
  have HP:=FormulaSignSlotRadialProviderRecordPrefix.word_value
    (FormulaSignSlotRadialProviderAtomic.root q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) _ (start_fit q) i hi
  have HM : FormulaSignSlotRadialProviderAtomic.initial q+preparedStart q≤
      FormulaSignSlotRadialProviderRecordPlan.fullCount (FormulaSignSlotRadialProviderAtomic.root q) :=by
    change FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)+preparedStart q≤
      FormulaSignSlotRadialProviderRecordPlan.count (FormulaSignSlotRadialProviderAtomic.root q)+
        IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q)
    exact Nat.add_le_add_left (start_fit q) _
  have HB : FormulaSignSlotRadialProviderAtomic.initial q+preparedStart q-1-i<
      FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q) :=by
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
    simp only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair]
    omega
  have HE:=FormulaSignSlotRadialProviderFieldEquality.point_env
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) _ HB
  have HP' : (O (FormulaSignSlotRadialProviderAtomic.root q) (preparedStart q) (start_fit q)).point (oldNatural q hv) i=
      FormulaSignSlotRadialProviderAtomic.bankField
        (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
        (FormulaSignSlotRadialProviderAtomic.full_valid q hv)
        (FormulaSignSlotRadialProviderAtomic.initial q+preparedStart q-1-i) :=by
    simpa only [oldNatural,FormulaSignSlotRadialProviderAtomic.initial,
      FormulaSignSlotRadialProviderRecordPrefix.context,FormulaSignSlotRadialProviderAtomic.context] using HP
  refine HP'.trans ?_
  unfold originalNaturalValues originalField
  rw [originalBirth_eq q hv]
  exact HE.symm

theorem canonical_parent_realizes (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    IntegralMixedIntegerRealization.Realizes ((G).state (K (canonical q))) (originalNaturalValues q hv) :=by
  have HO:=canonical_observation q hv
  have HR : (IntegralFramedPhysicalPrefixObservation.atRoot P D (pairFst (K (canonical q)))
      (prefixLength P (K (canonical q))) (min_le_right _ _)).Roots (oldNatural q hv) :=by
    rw [HO]
    simpa only [oldNatural] using prepared_prefix_roots q hv
  have HReal:=family_realizes P D H (K (canonical q)) (oldNatural q hv) HR
  apply realized_congr _ _ _ HReal
  intro i hi
  have HI : i<FormulaSignSlotRadialProviderAtomic.initial q+preparedStart q :=by
    rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth,prepared_birth q hv,prepared_initial] at hi
    exact hi
  exact (congrArg (fun obs : IntegralMixedFramedRunObservation.Data=>obs.point (oldNatural q hv) i) HO).trans
    ((congrArg (fun obs : IntegralMixedFramedRunObservation.Data=>obs.point (oldNatural q hv) i)
      (prepared_old_observation q hv)).trans (old_point q hv i HI))

theorem actual_parent_birth (q w : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    (G).birth (K (query (pair q w)))=originalBirth q :=
  (FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false _).trans
    (query_birth q w (count_positive q hv))

theorem exists_parent_word (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    ∃w,∃hp : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderCriticalPrefixes.input false) (query (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q w))),
      w.length=parentWidth q ∧
      ∀i : Fin ((G).birth (K (query (pair q w)))),
        FormulaSignSlotRadialProviderCriticalInterval.parentValues
          (query (pair q w)) hp i=
            originalNaturalValues q hv i.val :=by
  have HReal:=canonical_parent_realizes q hv
  obtain ⟨w,hp0,hlen,HP⟩:=IntegralFramedPhysicalSquare.exists_realized P D H L F C hs K
    (FormulaSignSlotRadialProviderCriticalPrefixes.positive false)
    (canonical q) (originalNaturalValues q hv) HReal
  have HE : pairFst (canonical q)=pairFst (query (pair q w)):=
    (root_word q []).trans (root_word q w).symm
  have hp' : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderCriticalPrefixes.input false) (query (pair q w)) w:=
    (FormulaSignSlotRadialProviderCriticalParentContext.valid_iff _ _ w HE).mp hp0
  have hp : SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderCriticalPrefixes.input false) (query (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q w))):=by
    rw [query_parentWord]
    exact hp'
  refine ⟨w,hp,hlen,?_⟩
  intro i
  have HB : (G).birth (K (canonical q))=
      (G).birth (K (query (pair q w))):=
    (actual_parent_birth q [] hv).trans (actual_parent_birth q w hv).symm
  let j : Fin ((G).birth (K (canonical q))):=⟨i.val,i.isLt.trans_eq HB.symm⟩
  have HT:=FormulaSignSlotRadialProviderCriticalParentContext.point_eq
    (canonical q) (query (pair q w)) w HE hp0 hp' j i rfl
  have HPoint : IntegralFramedPhysicalSquare.point P D H L F C hs K
      (FormulaSignSlotRadialProviderCriticalPrefixes.positive false)
      (query (pair q w)) w hp' i=originalNaturalValues q hv i.val:=
    HT.symm.trans (HP j)
  have HPoint' : IntegralFramedPhysicalSquare.point P D H L F C hs K
      (FormulaSignSlotRadialProviderCriticalPrefixes.positive false)
      (query (pair q w))
      (IntegralMixedPhysicalCriticalQuery.parentWord (query (pair q w))) hp i=
        originalNaturalValues q hv i.val:=by
    simpa only [query_parentWord] using HPoint
  exact (IntegralFramedPhysicalSquare.bank_naturalPoint P D H L F C hs K
    (FormulaSignSlotRadialProviderCriticalPrefixes.positive false)
    (query (pair q w)) _ hp i).trans HPoint'


end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
