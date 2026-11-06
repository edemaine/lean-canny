/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowQuotients
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowMeanRoots
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRankReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalNearWord
/-! # Native provider coordinate witnesses have one genuine geometric Near meaning -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep Polynomial IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS
local notation "hf"=>FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive
local notation "hd"=>FormulaSignSlotRadialProviderAtomic.Cuts.fallback
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe

noncomputable def originalValues (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u)) :=
  originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv

theorem originalValue_field (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (i : ℕ) (hi : i<FormulaSignSlotRadialProviderRecordPlan.fullCount
      (FormulaSignSlotRadialProviderAtomic.root q)) :
    originalValue q hv i=FormulaSignSlotRadialProviderAtomic.field q hv i :=by
  have HC:=FormulaSignSlotRadialProviderFieldEquality.count_eq (FormulaSignSlotRadialProviderAtomic.context q)
  simp only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair] at HC
  have HI : i<FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q):=by
    simpa only [FormulaSignSlotRadialProviderAtomic.context] using hi.trans_eq HC.symm
  simpa only [originalValue,FormulaSignSlotRadialProviderAtomic.field] using
    FormulaSignSlotRadialProviderFieldEquality.point_env (FormulaSignSlotRadialProviderAtomic.context q)
      (FormulaSignSlotRadialProviderAtomic.word q) (FormulaSignSlotRadialProviderAtomic.full_valid q hv) i HI

def QuotientsAt (F : IntegralMixedCutSource.Family) (old : List Bool)
    (φ : (F.state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : ℕ→ℝ) : Prop :=
  ∀i : Fin (F.birth old),φ ((F.state old).bank.numerator i)/((F.state old).bank.denominator i:ℝ)=
    values (F.birth old-1-i.val)

private theorem actual_birth (mode : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    (G).birth (parentKey mode z)=parentBirth mode z :=
  (parent_birth_actual mode z hv).trans (parentBirth_eq mode z (row_count_positive z hv)).symm

private theorem native_parent_agreement (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hO : SquareSampleCompleteVertices.Valid (Input (terminal false) (positive false))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u))
    (hM : SquareSampleCompleteVertices.Valid (Input (terminal true) (positive true))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u))
    (hFO : (G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
      (G).birth (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
    (hFM : (G).birth (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
      (G).birth (terminal true (FormulaSignSlotRadialProviderProperRowWitness.key u)))
    (φ : ((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : ((G).state (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : Interprets false _ _ hO hFO φ) (hψ : Interprets true _ _ hM hFM ψ) :
    ∀(i : Fin ((G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))))
      (j : Fin ((G).birth (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u)))),i.val=j.val→
      φ (((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.numerator i)/
        (((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.denominator i:ℝ)=
      ψ (((G).state (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.numerator j)/
        (((G).state (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.denominator j:ℝ) :=by
  have HO:=quotients_original false right u hv HL hO hFO φ hφ
  have HM:=quotients_original true right u hv HL hM hFM ψ hψ
  have HB : (G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))=
      (G).birth (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u)):=
    (parent_birth_actual false _ hv).trans (parent_birth_actual true _ hv).symm
  intro i j hij
  have HE : (G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-i.val=
      (G).birth (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-j.val:=congrArg₂ (fun a b : ℕ=>a-1-b) HB hij
  exact (HO i).trans ((congrArg (originalValue (FormulaSignSlotRadialProviderProperRowWitness.atomic u) hv) HE).trans (HM j).symm)

noncomputable def NearReceipt (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u)) : Prop:=
  ∃hw : SquareSampleCompleteVertices.Valid (Input (terminal false) (positive false))
    (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u),
  ∃hfit : (G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
    (G).birth (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)),
  ∃φ : ((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    Interprets false _ _ hw hfit φ ∧
    QuotientsAt G (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u)) φ
      (originalValues u hv) ∧
    IntegralMixedSelectedCoordinateEndpoint.Near
      ((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))) ((G).birth_bound _)
      ((G).rule (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))) φ
      (originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (originalValues u hv (oldProducer right (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))
        (get P Field.slot13 (parent false (FormulaSignSlotRadialProviderProperRowWitness.key u))))
      (Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u))
      (originalValues u hv (pointProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)))

attribute [local irreducible] NearReceipt

private theorem native_center_value (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal false) (positive false))
      (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u))
    (hfit : creating (FormulaSignSlotRadialProviderProperRowWitness.key u)≤
      (G).birth (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
    (hi : centerIndex right (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      (IntegralMixedFramedBankSnapshotBits.atKey P BP BH
        (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u))).count) :
    IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P BP BH (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal false)
        (positive false) (FormulaSignSlotRadialProviderProperRowWitness.key u)
        (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw)
      ⟨centerIndex right (FormulaSignSlotRadialProviderProperRowWitness.key u),hi⟩=
      if right then originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))
      else originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
  have HP : oldProducer right (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u):=by
    cases right
    · exact HL.1.2.2.1
    · exact HL.1.2.2.2.1
  have HE:=native_scalar_value false right u hv HL hw _ HP hfit
  rw [IntegralFramedPhysicalSquare.scalarTuple_point]
  cases right <;> simpa only [centerIndex,count,IntegralMixedFramedBankSnapshotBits.atKey,originalValues,
    Bool.false_eq_true,ite_false,ite_true] using HE

theorem native_near_hom (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hchild : pointProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (hab : originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u))<
      originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))) :
    NearReceipt right u hv :=by
  have HN:=HL.2.2.1
  simp only [FormulaSignSlotRadialProviderProperRowWitness.query,nearLanguage,IntegralFramedPhysicalNear.guarded,
    Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] at HN
  obtain ⟨hmeta,hw,HA⟩:=HN
  have HF : (G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
      (G).birth (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
    simpa only [parentKey,IntegralMixedFramedTerminalCoordinateHeadBits.Valid,
      IntegralMixedFramedCoordinateCoefficientSpaceBits.arity,IntegralMixedFramedBankSnapshotBits.atKey] using hmeta.2.1
  have HC:=row_count_positive (FormulaSignSlotRadialProviderProperRowWitness.key u) hv
  have HB : creating (FormulaSignSlotRadialProviderProperRowWitness.key u)≤
      (G).birth (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)):=
    ((actual_birth false _ hv).trans (parentBirth_eq false _ HC)).symm.trans_le HF
  have HAnchor:=native_center_value right u hv HL hw HB hmeta.2.2.2.1
  have HBackend:=IntegralFramedPhysicalNear.exists_near_iff P BP BH BL BF BC BS
    (parent false) (terminal false)
    (centerIndex right) (pointIndex false false)
    (positive false) hf hd right
    (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u)
    hw hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2.1 hmeta.2.2.2.2
    (a:=originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
    (b:=originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))) hab HAnchor
    (Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u))
  obtain ⟨φ,hγ,HNearIff⟩:=HBackend
  have HCanon:=(IntegralFramedPhysicalNear.accept_rank_word P BP BH BL BF BC BS
    (parent false) (terminal false)
    (centerIndex right) (pointIndex false false)
    (positive false) hf hd right
    (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u)
    (FormulaSignSlotRadialProviderProperRowWitness.rank u)).mp HA
  have HNear:=HNearIff.mp HCanon
  have HY:=native_scalar_value false right u hv HL hw _ hchild HB
  have HS : IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P BP BH (terminal false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal false)
        (positive false) (FormulaSignSlotRadialProviderProperRowWitness.key u)
        (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw)
      ⟨pointIndex false false (FormulaSignSlotRadialProviderProperRowWitness.key u),hmeta.2.2.2.2⟩=
      originalValues u hv (pointProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    simpa only [pointIndex,count,IntegralMixedFramedBankSnapshotBits.atKey,originalValues] using HY
  rw [HS] at HNear
  have HG : Interprets false (FormulaSignSlotRadialProviderProperRowWitness.key u)
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord false u) hw HF φ:=by
    simpa only [Interprets,parentKey] using hγ
  have HOrig:=quotients_original false right u hv HL hw HF φ HG
  have HOriginal : QuotientsAt G (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u)) φ
      (originalValues u hv):=by
    simpa only [QuotientsAt,originalValues] using HOrig
  unfold NearReceipt
  refine ⟨hw,HF,φ,HG,HOriginal,?_⟩
  have Hend : (if right then originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))
      else originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)))=
      originalValues u hv (oldProducer right (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
    cases right <;> rfl
  simpa only [Hend,parentKey] using HNear

noncomputable def RankReceipt (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u)) : Prop:=
  ∃hw : SquareSampleCompleteVertices.Valid (Input (terminal true) (positive true))
    (FormulaSignSlotRadialProviderProperRowWitness.key u) (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u),
  ∃hfit : (G).birth (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
    (G).birth (terminal true (FormulaSignSlotRadialProviderProperRowWitness.key u)),
  ∃ψ : ((G).state (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    Interprets true _ _ hw hfit ψ ∧
    let p:=(selected ((G).state (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))) ((G).birth_bound _)
      ((G).rule (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))
        (get P Field.slot13 (parent true (FormulaSignSlotRadialProviderProperRowWitness.key u)))) ψ).map (evalRingHom 0)
    let y:=originalValues u hv (pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))
    y∈p.roots.toFinset ∧OrderedRealRootWindow.rank p.roots.toFinset y=Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u)

attribute [local irreducible] RankReceipt

theorem native_rank_hom (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hmid : pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u)) :
    RankReceipt u hv :=by
  have HR:=HL.2.2.2.1
  simp only [FormulaSignSlotRadialProviderProperRowWitness.query] at HR
  obtain ⟨hmeta,hw,HK⟩:=(rankLanguage_iff (FormulaSignSlotRadialProviderProperRowWitness.key u)
    (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u) (FormulaSignSlotRadialProviderProperRowWitness.rank u)).mp HR
  unfold RankAt IntegralFramedZeroTarskiStatistic.RankAt at HK
  obtain ⟨ψ,hγ,HK⟩:=HK
  have HF : (G).birth (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))≤
      (G).birth (terminal true (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
    simpa only [parentKey,IntegralMixedFramedTerminalCoordinateHeadBits.Valid,
      IntegralMixedFramedCoordinateCoefficientSpaceBits.arity,IntegralMixedFramedBankSnapshotBits.atKey] using hmeta.2.1
  have HC:=row_count_positive (FormulaSignSlotRadialProviderProperRowWitness.key u) hv
  have HB : creating (FormulaSignSlotRadialProviderProperRowWitness.key u)≤
      (G).birth (terminal true (FormulaSignSlotRadialProviderProperRowWitness.key u)):=
    ((actual_birth true _ hv).trans (parentBirth_eq true _ HC)).symm.trans_le HF
  have HY:=native_scalar_value true right u hv HL hw _ hmid HB
  have HS : IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P BP BH (terminal true (FormulaSignSlotRadialProviderProperRowWitness.key u)))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal true)
        (positive true) (FormulaSignSlotRadialProviderProperRowWitness.key u)
        (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u) hw)
      ⟨pointIndex true true (FormulaSignSlotRadialProviderProperRowWitness.key u),hmeta.2.2.2.2⟩=
      originalValues u hv (pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)):=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    simpa only [pointIndex,count,IntegralMixedFramedBankSnapshotBits.atKey,originalValues] using HY
  dsimp only at HK
  rw [HS] at HK
  have HG : Interprets true (FormulaSignSlotRadialProviderProperRowWitness.key u)
      (FormulaSignSlotRadialProviderProperRowWitness.ownWord true u) hw HF ψ:=by
    simpa only [Interprets,parentKey] using hγ
  unfold RankReceipt
  exact ⟨hw,HF,ψ,HG,HK⟩

private theorem reverse_reference (a b p i : ℕ) (hab : a=b) (hp : p<b) (hi : i=b-1-p) :
    a-1-i=p :=by omega

private theorem mean_reference_value (side right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (φ : ((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (H : QuotientsAt G (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u)) φ
      (originalValues u hv)) :
    φ (((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.numerator
      (actualMeanReference side (FormulaSignSlotRadialProviderProperRowWitness.key u) hv HL.1))/
      (((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))).bank.denominator
        (actualMeanReference side (FormulaSignSlotRadialProviderProperRowWitness.key u) hv HL.1):ℝ)=
      originalValues u hv (oldProducer side (FormulaSignSlotRadialProviderProperRowWitness.key u)) :=by
  have HG:=parent_good false (FormulaSignSlotRadialProviderProperRowWitness.key u)
    (row_count_positive _ hv) HL.1
  have HP : oldProducer side (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      parentBirth false (FormulaSignSlotRadialProviderProperRowWitness.key u):=by
    cases side
    · exact HG.2.2.1
    · exact HG.2.2.2.1
  have HR : (actualMeanReference side (FormulaSignSlotRadialProviderProperRowWitness.key u) hv HL.1).val=
      parentBirth false (FormulaSignSlotRadialProviderProperRowWitness.key u)-1-
        oldProducer side (FormulaSignSlotRadialProviderProperRowWitness.key u) :=by
    simp only [actualMeanReference,meanReference,IntegralMixedChronologicalMidpoint.reference,Fin.val_mk]
  have HI : (G).birth (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))-1-
      (actualMeanReference side (FormulaSignSlotRadialProviderProperRowWitness.key u) hv HL.1).val=
      oldProducer side (FormulaSignSlotRadialProviderProperRowWitness.key u) :=
    reverse_reference _ _ _ _ (actual_birth false _ hv) HP HR
  simpa only [HI] using H (actualMeanReference side (FormulaSignSlotRadialProviderProperRowWitness.key u) hv HL.1)

noncomputable def CoordinateAt (right : Bool) (z : List Bool) (values : ℕ→ℝ) : Prop:=
  ∃φ : ((G).state (parentKey false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    QuotientsAt G (parentKey false z) φ
      values ∧
    IntegralMixedSelectedCoordinateEndpoint.Near
      ((G).state (parentKey false z)) ((G).birth_bound _)
      ((G).rule (parentKey false z)) φ
      (values (oldProducer false z))
      (values (oldProducer true z))
      (values (oldProducer right z))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey false z)
        (get P Field.slot13 (parent false z)))
      (IntegralMixedSelectedRootRank.rank
        ((G).state (parentKey false z)) ((G).birth_bound _)
        ((G).rule (parentKey false z)) φ
        ((values (oldProducer false z)+
          values (oldProducer true z))/2)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey false z)
          (get P Field.slot13 (parent false z)))
        (values (pointProducer true z)))
      (values (pointProducer false z))


attribute [local irreducible] CoordinateAt

noncomputable def CoordinateOutcome (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u)) : Prop:=
  CoordinateAt right (FormulaSignSlotRadialProviderProperRowWitness.key u)
    (originalValues u hv)

attribute [local irreducible] CoordinateOutcome

theorem native_coordinate_outcome (right : Bool) (u : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (FormulaSignSlotRadialProviderProperRowWitness.atomic u))
    (HL : u∈FormulaSignSlotRadialProviderProperRowWitness.language right)
    (hchild : pointProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (hmid : pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)<
      creating (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (hab : originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u))<
      originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))) :
    CoordinateOutcome right u hv :=by
  have HN:=native_near_hom right u hv HL hchild hab
  unfold NearReceipt at HN
  obtain ⟨hO,hFO,φ,hφ,HOriginal,HNear⟩:=HN
  have HM:=native_rank_hom right u hv HL hmid
  unfold RankReceipt at HM
  obtain ⟨hM,hFM,ψ,hψ,HMem,Hrank⟩:=HM
  have HAgree:=native_parent_agreement right u hv HL hO hM hFO hFM φ ψ hφ hψ
  let jo:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G
    (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (get P Field.slot13 (parent false (FormulaSignSlotRadialProviderProperRowWitness.key u)))
  let jm:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G
    (parentKey true (FormulaSignSlotRadialProviderProperRowWitness.key u))
    (get P Field.slot13 (parent true (FormulaSignSlotRadialProviderProperRowWitness.key u)))
  have HJ : jo.val=jm.val:=(selected_coordinate false _ hv HL.1).trans
    (selected_coordinate true _ hv HL.1).symm
  have HRoots:=actual_mean_roots (FormulaSignSlotRadialProviderProperRowWitness.key u) hv HL.1
  unfold MeanRootsAgree at HRoots
  have HR:=HRoots φ ψ HAgree jo jm HJ
  rw [mean_reference_value false right u hv HL φ HOriginal,
    mean_reference_value true right u hv HL φ HOriginal] at HR
  rw [HR] at Hrank
  have HCode : Nat.fromBitsLE (FormulaSignSlotRadialProviderProperRowWitness.rank u)=
      IntegralMixedSelectedRootRank.rank
        ((G).state (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))) ((G).birth_bound _)
        ((G).rule (parentKey false (FormulaSignSlotRadialProviderProperRowWitness.key u))) φ
        ((originalValues u hv (oldProducer false (FormulaSignSlotRadialProviderProperRowWitness.key u))+
          originalValues u hv (oldProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u)))/2) jo
        (originalValues u hv (pointProducer true (FormulaSignSlotRadialProviderProperRowWitness.key u))) :=by
    symm
    simpa only [IntegralMixedSelectedRootRank.rank,IntegralMixedFrozenFrameSectionCode.roots,
      IntegralMixedFrozenFrameSectionCode.polynomial,OrderedRealRootWindow.rank] using Hrank
  rw [HCode] at HNear
  unfold CoordinateOutcome CoordinateAt
  exact ⟨φ,HOriginal,HNear⟩


end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
