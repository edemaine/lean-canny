/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedCutReceipt
/-! # Exact native cut guards are equivalent to own-prefix receipts -/
@[expose] public section
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
local notation "G"=>family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedPhysicalFieldEquality.point IntegralMixedMarkedPrefixObservation.observation

private theorem native_fit (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :
    birth P (IntegralFramedPhysicalTraceCutSource.parent B (IntegralMixedPhysicalMarkedTest.sampleContext root)
      (List.replicate b true))<(G).birth ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext root)):=by
  have HB:=parent_birth hn ht ha hR0 root b hb
  have HC :(G).birth ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext root))=
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    change IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (IntegralMixedPhysicalMarkedTest.sampleContext root)=_
    rw [IntegralMixedPhysicalFieldEquality.count_eq]
    simp only [IntegralMixedPhysicalMarkedTest.sampleContext,pairFst_pair]
  simpa only [parent] using HB.trans_lt (hb.trans_eq HC.symm)

theorem ownReceipt_of_guard (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w)
    (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root)
    (hc :IntegralFramedCreatingCut.ParentCut P D (parent hn ht ha hR0 root (number n root+8+j)))
    (hg :IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha (radius_binary hR0) false
      (IntegralMixedPhysicalCutCoefficientSemantics.stage root w (List.replicate (number n root+8+j) true))) :
    ownReceipt hn ht ha hR0 root w hw j hj:=by
  let b:=number n root+8+j
  let key:=saved hn ht ha hR0 root b
  have HB :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;dsimp only [b];omega
  have HBirth:=parent_birth hn ht ha hR0 root b HB
  have HAct:=cut_active hn ht ha hR0 root b HB
  have HC :IntegralFramedCreatingCut.IsCut (instruction P D key).command:=hc
  obtain ⟨φ,hφ,hcg,hroot⟩:=(IntegralMixedPhysicalCutCoefficientSemantics.guards_iff_factor_receipt
    hn ht ha (radius_binary hR0) false root w (List.replicate b true) hw
    (native_fit hn ht ha hR0 root b HB) (by simpa only [parent,List.length_replicate] using HBirth)
    HAct hc).mp hg
  apply (IntegralMixedPrefixSnapshot.familyCutReceipt_iff P D H key _ _ HC).mpr
  have HValues:=quotients_at hn ht ha hR0 root w hw j hj key rfl φ hφ
  have HQ:=bankQuotient_field hn ht ha hR0 root w hw b HB
  refine ⟨φ,HValues,hcg,?_⟩
  exact (congrArg (fun a :ℝ=>(IntegralMixedRelativeCuts.factor ((G).state key) ((G).birth_bound key)
    ((G).rule key) ((G).kind key)).eval₂ φ.toRingHom a) HQ).symm.trans hroot

theorem guard_of_ownReceipt (root w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX root) w)
    (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root)
    (hc :IntegralFramedCreatingCut.ParentCut P D (parent hn ht ha hR0 root (number n root+8+j)))
    (hr :ownReceipt hn ht ha hR0 root w hw j hj) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha (radius_binary hR0) false
      (IntegralMixedPhysicalCutCoefficientSemantics.stage root w (List.replicate (number n root+8+j) true)):=by
  let b:=number n root+8+j
  let key:=saved hn ht ha hR0 root b
  have HB :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;dsimp only [b];omega
  have HBirth:=parent_birth hn ht ha hR0 root b HB
  have HAct:=cut_active hn ht ha hR0 root b HB
  have HC :IntegralFramedCreatingCut.IsCut (instruction P D key).command:=hc
  obtain ⟨φ,hv,hcg,hroot⟩:=(IntegralMixedPrefixSnapshot.familyCutReceipt_iff P D H key _ _ HC).mp hr
  have HFit : (G).birth key≤(G).birth ((B).key (IntegralMixedPhysicalMarkedTest.sampleContext root)):=by
    exact ((geometry P D H).birth (parent hn ht ha hR0 root b)).trans_le
      (native_fit hn ht ha hR0 root b HB).le
  obtain ⟨ψ,hψ,_⟩:=IntegralMixedPhysicalCutCoefficientSemantics.exists_coefficient_evaluation
    hn ht ha (radius_binary hR0) false root w (List.replicate b true) hw HFit HAct
  have HValues:=quotients_at hn ht ha hR0 root w hw j hj key rfl ψ hψ
  have HE :φ=ψ:=IntegralMixedPrefixSnapshot.hom_eq_of_quotients ((G).state key)
    (family_canonical P D H key) φ ψ (fun i=>(hv i).trans (HValues i).symm)
  have HQ:=bankQuotient_field hn ht ha hR0 root w hw b HB
  have HC' :IntegralMixedRelativeCuts.CoefficientGuards ((G).state key) ((G).birth_bound key)
      ((G).rule key) ψ ((G).kind key) ((G).degree key):=by simpa only [HE] using hcg
  have HR' :(IntegralMixedRelativeCuts.factor ((G).state key) ((G).birth_bound key) ((G).rule key)
      ((G).kind key)).eval₂ ψ.toRingHom
      (IntegralMixedPhysicalCutCoefficientSemantics.bankQuotient hn ht ha (radius_binary hR0) false root w
        (List.replicate b true) hw)=0:=by
    exact (congrArg (fun a :ℝ=>(IntegralMixedRelativeCuts.factor ((G).state key) ((G).birth_bound key)
      ((G).rule key) ((G).kind key)).eval₂ ψ.toRingHom a) HQ).trans (by simpa only [HE] using hroot)
  exact IntegralMixedPhysicalCutCoefficientSemantics.guards_of_factor_receipt
    hn ht ha (radius_binary hR0) false root w (List.replicate b true) hw
    (native_fit hn ht ha hR0 root b HB) (by simpa only [parent,List.length_replicate] using HBirth)
    HAct ψ hψ HC' HR'

end LeanCanny.Encoding.IntegralMixedMarkedCutStage
