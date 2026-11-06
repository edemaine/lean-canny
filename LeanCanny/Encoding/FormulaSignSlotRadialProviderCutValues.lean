/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # Actual cut head and retained values on the same provider word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderRecordPrefix (context cutParent cutSaved natural observation)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "G" => family P D H

private theorem bank_birth (r : List Bool) : (G).birth ((B).key (context r))=
    FormulaSignSlotRadialProviderRecordPlan.fullCount r :=
  (family_birth P D H ((B).key (context r))).trans (FormulaSignSlotRadialProviderRecordPrefix.full_prefix r)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  IntegralMixedFramedHistoryFamilyBits.family IntegralFramedPhysicalSuffixTest.rawTuple
  SquareSampleCompleteCoordinateSign.value

variable (r w : List Bool)
  (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (context r) w) (b : ℕ)

noncomputable def quotient :=
  (IntegralMixedFramedBankObservation.ofState ((G).state ((B).key (context r)))).point
    (IntegralFramedPhysicalSuffixTest.rawTuple B (context r) w hw) ((G).birth ((B).key (context r))-b-1)

theorem quotient_field (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    quotient r w hw b=FormulaSignSlotRadialProviderAtomic.bankField (context r) w hw b := by
  let i : Fin ((G).birth ((B).key (context r))) := ⟨(G).birth ((B).key (context r))-b-1,by rw [bank_birth];omega⟩
  have HP := IntegralFramedPhysicalSuffixTest.bank_point_observation B (context r) w hw i
  have HB : b<(IntegralMixedFramedBankSnapshotBits.atKey P D H ((B).key (context r))).count := by
    change b<(G).birth ((B).key (context r))
    rw [bank_birth]
    exact hb
  have HE := IntegralFramedPhysicalBankTerm.env_chronological B T FormulaSignSlotRadialProviderAtomic.bank_represents
    (context r) w hw b HB
  unfold quotient
  refine HP.trans (Eq.trans ?_ HE.symm)
  apply congrArg (IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context r) w hw)
  apply Fin.ext
  change (G).birth ((B).key (context r))-b-1=(G).birth ((B).key (context r))-1-b
  omega

theorem head_packet (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    FormulaSignSlotRadialProviderAtomic.Cuts.head (stage r w b)=InfinitesimalSign.encode
      (SignType.sign (IntegralFramedPhysicalSuffixTest.rawTuple B (context r) w hw
        (FormulaSignSlotRadialProviderRecordPlan.fullCount r-b-1))) := by
  let m := FormulaSignSlotRadialProviderRecordPlan.fullCount r
  let i : Fin ((IntegralFramedBankQuery.input B).count (context r)) :=
    ⟨m-b-1,by change m-b-1<(G).birth ((B).key (context r));rw [bank_birth];dsimp only [m];omega⟩
  have HP := IntegralFramedPhysicalSuffixTest.scalar_column_sign B (context r) w hw T
    FormulaSignSlotRadialProviderAtomic.bank_represents i
  simpa only [FormulaSignSlotRadialProviderAtomic.Cuts.head,Function.comp_apply,
    FormulaSignSlotRadialProviderAtomic.Cuts.headQuery,FormulaSignSlotRadialProviderAtomic.Cuts.sample,
    FormulaSignSlotRadialProviderAtomic.Cuts.column,FormulaSignSlotRadialProviderAtomic.Cuts.age,
    FormulaSignSlotRadialProviderAtomic.Cuts.creatingRoot,FormulaSignSlotRadialProviderAtomic.Cuts.ownWord,
    FormulaSignSlotRadialProviderAtomic.Cuts.creatingStage,IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutGuards.word,IntegralFramedTraceCutGuards.stage,
    stage,IntegralFramedTraceCutScan.stagePacket,pairFst_pair,pairSnd_pair,List.length_replicate,
    i,m,context] using HP

theorem head_zero_iff (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) :
    FormulaSignSlotRadialProviderAtomic.Cuts.head (stage r w b)=InfinitesimalSign.encode 0 ↔
      IntegralFramedPhysicalSuffixTest.rawTuple B (context r) w hw
        (FormulaSignSlotRadialProviderRecordPlan.fullCount r-b-1)=0 := by
  rw [head_packet r w hw b hb]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

theorem coefficient_evaluation_at (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r)
    (φ : ((G).state (cutSaved r b)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : Generators r w hw b φ) :
    ∀e k,e≤2^(P).width r→k≤2^(P).width r→
      FormulaSignSlotRadialProviderAtomic.Cuts.sign (FiniteCoefficientSignScan.query (stage r w b) e k)=
        InfinitesimalSign.encode (SignType.sign (φ ((IntegralMixedRelativeCuts.factor ((G).state (cutSaved r b))
          ((G).birth_bound (cutSaved r b)) ((G).rule (cutSaved r b))
          (IntegralMixedRelativeCuts.atChoice ((G).rule (cutSaved r b)) ((G).kind (cutSaved r b)) k)).coeff e))) := by
  obtain ⟨ψ,hψ,HE⟩ := coefficient_evaluation r w hw b hb
  have HX : ψ=φ := ((G).state (cutSaved r b)).sampler.scalarPrefix.basis.algHom_ext ψ φ
    (fun i=>(hψ i).trans (hφ i).symm)
  cases HX
  exact HE

variable (j : ℕ) (hj : j<IntegralMixedCausalRecordPlanBits.count r)
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "old" => cutSaved r (N r+j)

theorem quotients_at
    (φ : ((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : Generators r w hw (N r+j) φ) :
    ∀i : Fin ((G).birth old),φ (((G).state old).bank.numerator i)/
      (((G).state old).bank.denominator i:ℝ)=
      (observation r j hj.le).point (natural r w hw) i.val := by
  have HB : N r+j<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    omega
  have HF : (G).birth old≤(G).birth ((B).key (context r)) :=
    (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth r _ HB).trans_le
      (HB.le.trans_eq (bank_birth r).symm)
  have HM : N r+j≤prefixLength P ((B).key (context r)) := by
    exact HB.le.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.full_prefix r).symm
  have HE : old=keyAt (pairFst ((B).key (context r))) (N r+j) (BinaryNatCode.encode 2) := by
    rw [FormulaSignSlotRadialProviderRecordPrefix.key_root]
    exact FormulaSignSlotRadialProviderRecordPrefix.cutSaved_eq r _ HB
  have HQ := IntegralFramedPhysicalTraceCutSource.quotient_observation B
    FormulaSignSlotRadialProviderAtomic.Cuts.key_context (context r) w hw (List.replicate (N r+j) true)
    old rfl (N r+j) HM (BinaryNatCode.encode 2) HE HF φ hφ
  have HObs : IntegralFramedPhysicalScalarObservation.atKeyObservation P D old=observation r j hj.le := by
    have H0 := congrArg (IntegralFramedPhysicalScalarObservation.atKeyObservation P D)
      (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_eq r (N r+j) HB)
    have H1 := IntegralFramedPhysicalScalarObservation.observation_keyAt P D r (N r+j)
      (BinaryNatCode.encode 2) (FormulaSignSlotRadialProviderRecordPrefix.bank_bound r j hj.le)
    exact H0.trans (H1.trans (FormulaSignSlotRadialProviderRecordPrefix.bank_observation r j hj.le))
  intro i
  exact (HQ i).trans (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>
    O.point (natural r w hw) i.val) HObs)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutReadback
