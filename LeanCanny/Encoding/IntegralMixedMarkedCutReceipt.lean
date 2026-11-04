/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixCutReceipt
public import LeanCanny.Encoding.IntegralMixedMarkedCutInterpretation
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutReceipt
public import LeanCanny.Encoding.IntegralMixedPhysicalChronologicalPoint
/-! # Native historical cut guards have an exact prefix-and-values receipt -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def familyCutReceipt (P :IntegralCriticalHistoryTask.Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key :List Bool) (values :ℕ→ℝ) (a :ℝ) :Prop:=
  (ofState ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)).CutReceipt ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
    (instruction P D key).command values a

theorem familyCutReceipt_iff (P :IntegralCriticalHistoryTask.Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key :List Bool) (values :ℕ→ℝ) (a :ℝ)
    (hc :IntegralFramedCreatingCut.IsCut (instruction P D key).command) :
    familyCutReceipt P D H key values a↔
      ∃φ :((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀i,φ (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.numerator i)/
          (((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.denominator i:ℝ)=values i.val) ∧
        IntegralMixedRelativeCuts.CoefficientGuards ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
          ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) φ ((IntegralMixedFramedHistoryFamilyBits.family P D H).kind key) ((IntegralMixedFramedHistoryFamilyBits.family P D H).degree key) ∧
        (IntegralMixedRelativeCuts.factor ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth_bound key)
          ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) ((IntegralMixedFramedHistoryFamilyBits.family P D H).kind key)).eval₂ φ.toRingHom a=0:=by
  cases he:(instruction P D key).command with
  | integer =>simp only [he,IntegralFramedCreatingCut.IsCut] at hc
  | critical =>simp only [he,IntegralFramedCreatingCut.IsCut] at hc
  | cut r k d hs hd=>
    have HS :selection P D H key=⟨r,k,d,hs⟩:=by simp only [selection,he]
    simp only [familyCutReceipt,Data.CutReceipt,ofState,IntegralMixedFramedHistoryFamilyBits.family,he]
    rw [HS]

theorem familyCutReceipt_transport (P :IntegralCriticalHistoryTask.Parameters) (D :Plan P) (H :IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key other :List Bool)
    (hs :ofState ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key)=ofState ((IntegralMixedFramedHistoryFamilyBits.family P D H).state other))
    (hc :HEq (instruction P D key).command (instruction P D other).command)
    (values next :ℕ→ℝ) (a :ℝ) (hv :∀i<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key,values i=next i) :
    familyCutReceipt P D H key values a↔familyCutReceipt P D H other next a:=
  Data.cutReceipt_transport _ _ _ _ _ _ hs hc values next a hv

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot

namespace LeanCanny.Encoding.IntegralMixedMarkedCutStage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalFieldEquality.point IntegralFramedPhysicalSquare.point

noncomputable def ownReceipt (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w)
    (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root):=
  IntegralMixedPrefixSnapshot.familyCutReceipt P D H (saved hn ht ha hR0 root (number n root+8+j))
    ((IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj.le).point
      (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 root w hw))
    (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX root) w hw (number n root+8+j))

theorem bankQuotient_field (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w)
    (b :ℕ) (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :
    IntegralMixedPhysicalCutCoefficientSemantics.bankQuotient hn ht ha (radius_binary hR0) false root w
      (List.replicate b true) hw=
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX root) w hw b:=by
  have HC :(G).birth ((B).key (CTX root))=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    change IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (CTX root)=_
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair]
  have HB :birth P (IntegralFramedPhysicalTraceCutSource.parent B (CTX root) (List.replicate b true))=b:=by
    simpa only [parent,IntegralMixedMarkedPrefixFieldReadback.context,IntegralMixedPhysicalMarkedTest.sampleContext]
      using parent_birth hn ht ha hR0 root b hb
  let i :Fin ((G).birth ((B).key (CTX root))):=⟨(G).birth ((B).key (CTX root))-b-1,by rw [HC];omega⟩
  have HP:=IntegralFramedPhysicalSuffixTest.bank_point_observation B (CTX root) w hw i
  have HF:=IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) (CTX root) w hw b
    (by rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H,HC];exact hb)
  have HIndex :(G).birth ((B).key (CTX root))-
      birth P (IntegralFramedPhysicalTraceCutSource.parent B (CTX root) (List.replicate b true))-1=i.val:=by
    rw [HB]
  have HQ :IntegralMixedPhysicalCutCoefficientSemantics.bankQuotient hn ht ha (radius_binary hR0) false root w
      (List.replicate b true) hw=
      (IntegralMixedFramedBankObservation.ofState ((G).state ((B).key (CTX root)))).point
        (IntegralFramedPhysicalSuffixTest.rawTuple B (CTX root) w hw) i.val:=by
    simpa only [IntegralMixedPhysicalCutCoefficientSemantics.bankQuotient,
      IntegralMixedMarkedPrefixFieldReadback.context,IntegralMixedPhysicalMarkedTest.sampleContext] using
      congrArg (fun idx=>(IntegralMixedFramedBankObservation.ofState ((G).state ((B).key (CTX root)))).point
        (IntegralFramedPhysicalSuffixTest.rawTuple B (CTX root) w hw) idx) HIndex
  refine HQ.trans (HP.trans (Eq.trans ?_ HF.symm))
  apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (CTX root) w hw)
  apply Fin.ext
  dsimp only [i]
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
  omega

end LeanCanny.Encoding.IntegralMixedMarkedCutStage
