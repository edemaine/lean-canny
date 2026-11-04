/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowMeanRule
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowQuotients
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowInterpretation
public import LeanCanny.Geometry.IntegralMixedBankValueInterpretation
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowValue
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankReadback
public import LeanCanny.Encoding.IntegralFramedPhysicalNearWord
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProducerBounds
public import LeanCanny.Encoding.IntegralMixedRoadmapProperOrder
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch
/-! # The native mean probe selects the ordinary midpoint coordinate roots -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedNumericalSweep Polynomial
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem mean_roots (A B : IntegralMixedPrefixSnapshot.Data) (he : A=B)
    (hm : A.birth≤A.horizon) (hl : B.birth≤B.horizon)
    (r : Rule A.ambient) (s : Rule B.ambient) (a b : Fin A.birth)
    (hs : HEq s (IntegralMixedMeanCenteredSweep.rule r a b))
    (hr : r.slope=commonDenominator A.state)
    (hc : Canonical A.state)
    (φ : A.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : B.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (H : ∀(i : Fin A.birth) (j : Fin B.birth),i.val=j.val→φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)=
      ψ (B.state.bank.numerator j)/(B.state.bank.denominator j:ℝ))
    (hz : r.critical.heights r.height=.constant 0)
    (h1 : r.critical.scales r.height=1)
    (j : Fin (A.ambient-r.critical.offset.val+1))
    (k : Fin (B.ambient-s.critical.offset.val+1)) (hj : j.val=k.val) :
    ((selected B.state hl s k ψ).map (evalRingHom 0)).roots=
      ((selected A.state hm r j φ).map (evalRingHom
        ((φ (A.state.bank.numerator a)/(A.state.bank.denominator a:ℝ)+
          φ (A.state.bank.numerator b)/(A.state.bank.denominator b:ℝ))/2))).roots :=by
  cases he
  have HS : s=IntegralMixedMeanCenteredSweep.rule r a b:=eq_of_heq hs
  subst s
  have HP : φ=ψ:=IntegralMixedBankValueInterpretation.hom_ext A.state hc φ ψ
    (fun i=>H i i rfl)
  subst ψ
  have HJ : j=k:=Fin.ext hj
  subst k
  let values : Fin A.birth→ℝ:=fun i=>φ (A.state.bank.numerator i)/(A.state.bank.denominator i:ℝ)
  have HZ : (r.critical.heights r.height).evaluate values=0:=by rw [hz];simp only [AffineExpr.evaluate,Int.cast_zero]
  rw [selected_specialize A.state hl (IntegralMixedMeanCenteredSweep.rule r a b) hr φ values (fun _=>rfl),
    selected_specialize A.state hm r hr φ values (fun _=>rfl)]
  rw [Polynomial.roots_C_mul _ (coordinateScale_ne_zero A.state hl _),
    Polynomial.roots_C_mul _ (coordinateScale_ne_zero A.state hm r),
    ←IntegralMixedMeanCenteredSweep.coordinateAt_mean A.source r a b values HZ h1 j]

private theorem raw_ordinary_normal_form {a b : ℕ} (w : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good a b w g j) (Q : ℤ) (hQ : Q≠0)
    : let r:=(IntegralMixedChronologicalCutCode.rawData a b w g j hg).rule Q hQ
    r.critical.heights r.height=.constant 0 ∧r.critical.scales r.height=1 :=by
  dsimp only
  let d:=IntegralMixedChronologicalFrameCode.descriptor a b w hg.1
  let hk:=IntegralMixedChronologicalCutCode.raw_fit a b w g j hg
  constructor
  · change (d.atom (FrozenCoordinateOrdering.permutation
      (IntegralMixedChronologicalSweepFrame.frame d hk).frozen
      (IntegralMixedChronologicalSweepFrame.next d hk))).value=.constant 0
    rw [(IntegralMixedChronologicalSweepFrame.prefix_frozen d hk).permutation]
    simp only [Equiv.refl_apply,IntegralMixedChronologicalFrame.Descriptor.atom,
      IntegralMixedChronologicalSweepFrame.next,Fin.val_mk,Nat.lt_irrefl,dite_false,
      IntegralMixedCausalRowConstructor.Atom.value]
  · rfl

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  parent terminal creating parentBirth root

private theorem ordinary_normal_form (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    let r:=(G).rule (parentKey hn ht ha hR0 false z)
    r.critical.heights r.height=.constant 0 ∧r.critical.scales r.height=1 :=by
  dsimp only
  rw [rule_at_parent hn ht ha hR0 false z (row_count_positive hn ht ha hR0 z hv) hg]
  simp only [parentData,Bool.false_eq_true,ite_false]
  exact raw_ordinary_normal_form _ _ _ _ _ _

private theorem actual_birth (mode : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    (G).birth (parentKey hn ht ha hR0 mode z)=parentBirth hn ht ha hR0 mode z :=by
  have HC:=row_count_positive hn ht ha hR0 z hv
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth P
    (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK) _).trans
      ((parentKey_prefix hn ht ha hR0 mode z HC).trans (parentBirth_eq hn ht ha hR0 mode z HC).symm)

noncomputable def actualMeanReference (side : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    Fin ((G).birth (parentKey hn ht ha hR0 false z)):=
  ⟨(meanReference hn ht ha hR0 side z hv hg).val,by
    rw [actual_birth hn ht ha hR0 false z hv]
    exact (meanReference hn ht ha hR0 side z hv hg).isLt⟩

def MeanRootsModel (F : IntegralMixedCutSource.Family) (o e : List Bool)
    (a b : Fin (F.birth o)) : Prop:=
  ∀φ : (F.state o).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  ∀ψ : (F.state e).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  (∀(i : Fin (F.birth o)) (j : Fin (F.birth e)),i.val=j.val→φ ((F.state o).bank.numerator i)/((F.state o).bank.denominator i:ℝ)=
    ψ ((F.state e).bank.numerator j)/((F.state e).bank.denominator j:ℝ))→
  ∀j : Fin (F.ambient o-(F.rule o).critical.offset.val+1),
  ∀k : Fin (F.ambient e-(F.rule e).critical.offset.val+1),j.val=k.val→
    ((selected (F.state e) (F.birth_bound e) (F.rule e) k ψ).map (evalRingHom 0)).roots=
    ((selected (F.state o) (F.birth_bound o) (F.rule o) j φ).map (evalRingHom
      ((φ ((F.state o).bank.numerator a)/((F.state o).bank.denominator a:ℝ)+
        φ ((F.state o).bank.numerator b)/((F.state o).bank.denominator b:ℝ))/2))).roots

theorem actual_mean_roots (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    MeanRootsModel G (parentKey hn ht ha hR0 false z) (parentKey hn ht ha hR0 true z)
      (actualMeanReference hn ht ha hR0 false z hv hg) (actualMeanReference hn ht ha hR0 true z hv hg) :=by
  intro φ ψ H j k hj
  have HC:=row_count_positive hn ht ha hR0 z hv
  have HN:=ordinary_normal_form hn ht ha hR0 z hv hg
  exact mean_roots (IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey hn ht ha hR0 false z)))
    (IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey hn ht ha hR0 true z)))
    (parent_state_snapshot_eq_valid hn ht ha hR0 z hv) _ _ _ _
    (actualMeanReference hn ht ha hR0 false z hv hg) (actualMeanReference hn ht ha hR0 true z hv hg)
    (actual_mean_rule hn ht ha hR0 z hv hg) (rule_current hn ht ha hR0 false z HC hg)
    (parent_canonical hn ht ha hR0 false z HC) φ ψ H
    HN.1 HN.2 j k hj

local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "BL"=>IntegralFramedBankQuery.Bank.nodes BK
local notation "BF"=>IntegralFramedBankQuery.Bank.factor BK
local notation "BC"=>IntegralFramedBankQuery.Bank.seed BK
local notation "BS"=>IntegralFramedBankQuery.Bank.bounds BK
local notation "Input"=>IntegralFramedPhysicalSquare.input P BP BH BL BF BC BS

private def NativeInterprets (mode : Bool) (z w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 mode) (positive hn ht ha hR0 mode)) z w)
    (hfit : (G).birth (parentKey hn ht ha hR0 mode z)≤(G).birth (terminal hn ht ha hR0 mode z))
    (φ : ((G).state (parentKey hn ht ha hR0 mode z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop:=
  ∀i : Fin ((G).birth (parentKey hn ht ha hR0 mode z)),φ (((G).state (parentKey hn ht ha hR0 mode z)).sampler.scalarPrefix.basis.generator i)=
    IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 mode)
      (positive hn ht ha hR0 mode) z w hw (UniformIntegralPowerSchedule.embed hfit i)^
        UniformIntegralPowerSchedule.weights ((G).cap (parentKey hn ht ha hR0 mode z))
          (2^(G).width (parentKey hn ht ha hR0 mode z)) ((G).birth (parentKey hn ht ha hR0 mode z)) i

private def QuotientAgreement (F : IntegralMixedCutSource.Family) (o e : List Bool)
    (φ : (F.state o).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (F.state e).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop:=
  ∀(i : Fin (F.birth o)) (j : Fin (F.birth e)),i.val=j.val→φ ((F.state o).bank.numerator i)/((F.state o).bank.denominator i:ℝ)=
    ψ ((F.state e).bank.numerator j)/((F.state e).bank.denominator j:ℝ)

private theorem point_chain (a b : ℕ→ℝ) (bound : ℕ)
    (H : ∀i<bound,a i=b i) (i j : ℕ) (hi : i<bound) (he : i=j) : a i=b j :=
  (H i hi).trans (congrArg b he)

attribute [local irreducible] IntegralMixedMarkedPrefixFieldReadback.parentPoint

private def NativeAgreementModel (u : List Bool) : Prop:=
  ∀(hO : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u))
    (hM : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord true u))
    (hfO : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))≤
      (G).birth (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))
    (hfM : (G).birth (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))≤
      (G).birth (terminal hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)))
    (φ : ((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : ((G).state (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (_hφ : NativeInterprets hn ht ha hR0 false _ _ hO hfO φ)
    (_hψ : NativeInterprets hn ht ha hR0 true _ _ hM hfM ψ),
    QuotientAgreement G (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))
      (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)) φ ψ

attribute [local irreducible] NativeAgreementModel NativeInterprets

private theorem native_parent_quotients (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right) :
    NativeAgreementModel hn ht ha hR0 u :=by
  unfold NativeAgreementModel
  intro hO hM hfO hfM φ ψ hφ hψ
  unfold NativeInterprets at hφ hψ
  obtain ⟨hO',hM',HE⟩:=IntegralMixedRoadmapProperRowWitness.parent_values_equal hn ht ha hR0 right u hv HL
  have HC:=row_count_positive hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u) hv
  have HPO:=statistic_parent_quotients hn ht ha hR0 false _ _ hv hO hfO φ hφ
  have HPM:=statistic_parent_quotients hn ht ha hR0 true _ _ hv hM hfM ψ hψ
  intro i j hij
  have HI : i.val<creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=
    i.isLt.trans_eq ((actual_birth hn ht ha hR0 false _ hv).trans (parentBirth_eq hn ht ha hR0 false _ HC))
  have HBO : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))=
      (IntegralMixedFramedHistoryFamilyBits.commands P BP
        (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).length:=by unfold IntegralMixedFramedHistoryFamilyBits.family;rfl
  have HBM : (G).birth (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))=
      (IntegralMixedFramedHistoryFamilyBits.commands P BP
        (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))).length:=by unfold IntegralMixedFramedHistoryFamilyBits.family;rfl
  have HVO : hO'=(valid_at_context hn ht ha hR0 false _ _).mp hO:=Subsingleton.elim _ _
  have HVM : hM'=(valid_at_context hn ht ha hR0 true _ _).mp hM:=Subsingleton.elim _ _
  cases HVO
  cases HVM
  have HOi :=HPO (Fin.cast HBO i)
  have HMj :=HPM (Fin.cast HBM j)
  have HEij:=point_chain _ _ _ HE i.val j.val HI hij
  exact HOi.trans (HEij.trans HMj.symm)

private noncomputable def originalValues (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u)) : ℕ→ℝ:=
  originalValue hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u) hv

private def QuotientsAt (F : IntegralMixedCutSource.Family) (old : List Bool)
    (φ : (F.state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : ℕ→ℝ) : Prop:=
  ∀i : Fin (F.birth old),φ ((F.state old).bank.numerator i)/((F.state old).bank.denominator i:ℝ)=
    values (F.birth old-1-i.val)

private def NativeOriginalModel (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u)) : Prop:=
  ∀hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false))
    (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u),
  ∀hf : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))≤
    (G).birth (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)),
  ∀φ : ((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
  NativeInterprets hn ht ha hR0 false _ _ hw hf φ→
    QuotientsAt G (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)) φ
      (originalValues hn ht ha hR0 u hv)

attribute [local irreducible] NativeOriginalModel originalValues IntegralMixedPhysicalFieldEquality.point

private theorem native_original_quotients (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right) :
    NativeOriginalModel hn ht ha hR0 u hv :=by
  unfold NativeOriginalModel
  intro hw hf φ hφ
  unfold NativeInterprets at hφ
  have HScan : IntegralMixedRoadmapProperRowWitness.fieldMatch hn ht ha hR0 false u∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=HL.2.2.2.2.1
  obtain ⟨hL,hR,HE⟩:=IntegralMixedRoadmapProperRowWitness.fieldMatch_sound hn ht ha hR0 false u HScan
  have HPL : hL=IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 _ hv:=Subsingleton.elim _ _
  have HPR : hR=(valid_at_context hn ht ha hR0 false _ _).mp hw:=Subsingleton.elim _ _
  cases HPL
  cases HPR
  have HC:=row_count_positive hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u) hv
  have HR:=root_count hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u) HC
  have HB : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))=
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=
    (actual_birth hn ht ha hR0 false _ hv).trans (parentBirth_eq hn ht ha hR0 false _ HC)
  have HM : IntegralMixedMarkedPrefixFieldReadback.parent n
      (root hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))=
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    unfold IntegralMixedMarkedPrefixFieldReadback.parent
    rw [root_number,HR]
    unfold creating IntegralMixedRoadmapBadProbePacket.creating
    omega
  have HPO:=statistic_parent_quotients hn ht ha hR0 false
    (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u) hv hw hf φ hφ
  intro i
  have HI0 : i.val<(G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)):=i.isLt
  have HI : i.val<creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=HI0.trans_eq HB
  have hOwn : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedMarkedPrefixFieldReadback.context (root hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralMixedRoadmapProperRowWitness.ownWord false u):=by
    simpa only [context,IntegralMixedMarkedPrefixFieldReadback.context] using
      (valid_at_context hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)
        (IntegralMixedRoadmapProperRowWitness.ownWord false u)).mp hw
  have HCh:=IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
    (root hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))
    (IntegralMixedRoadmapProperRowWitness.ownWord false u)
    hOwn (HC.trans_eq HR.symm) i.val (HI.trans_eq HM.symm)
  rw [HM] at HCh
  have HX:=HE (creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)-1-i.val) (by omega)
  have HIndex : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))-1-i.val=
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)-1-i.val:=congrArg (fun m : ℕ=>m-1-i.val) HB
  have HOrig : IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context (IntegralMixedRoadmapProperRowWitness.atomic u))
      (IntegralMixedRoadmapAtomic.word (IntegralMixedRoadmapProperRowWitness.atomic u))
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 _ hv)
      (creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)-1-i.val)=
      originalValues hn ht ha hR0 u hv (creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)-1-i.val):=by
    unfold originalValues originalValue;rfl
  exact ((HPO i).trans (HCh.trans HX.symm)).trans
    (HOrig.trans (congrArg (originalValues hn ht ha hR0 u hv) HIndex.symm))

local notation "hf"=>IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (radius_binary hR0) false
local notation "hd"=>IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (radius_binary hR0) false

private def NearHomModel (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u)) : Prop:=
  ∃hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false))
    (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u),
  ∃hfit : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))≤
    (G).birth (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)),
  ∃φ : ((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    NativeInterprets hn ht ha hR0 false _ _ hw hfit φ ∧
    QuotientsAt G (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)) φ
      (originalValues hn ht ha hR0 u hv) ∧
    IntegralMixedSelectedCoordinateEndpoint.Near
      ((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))) ((G).birth_bound _)
      ((G).rule (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))) φ
      (originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u)))
      (originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u)))
      (originalValues hn ht ha hR0 u hv (oldProducer right (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))
        (get P Field.slot13 (parent hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))))
      (Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u))
      (originalValues hn ht ha hR0 u hv (pointProducer hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))

attribute [local irreducible] NearHomModel

private theorem native_center_value (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
    (hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 false) (positive hn ht ha hR0 false))
      (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u))
    (hfit : creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)≤
      (G).birth (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))
    (hi : centerIndex hn ht ha hR0 right (IntegralMixedRoadmapProperRowWitness.key u)<
      (IntegralMixedFramedBankSnapshotBits.atKey P BP BH
        (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).count) :
    IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 false)
        (positive hn ht ha hR0 false) (IntegralMixedRoadmapProperRowWitness.key u)
        (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw)
      ⟨centerIndex hn ht ha hR0 right (IntegralMixedRoadmapProperRowWitness.key u),hi⟩=
      if right then originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u))
      else originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u)):=by
  have HP : oldProducer right (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    cases right
    · exact HL.1.2.2.1
    · exact HL.1.2.2.2.1
  have HE:=native_scalar_value hn ht ha hR0 false right u hv HL hw _ HP hfit
  rw [IntegralFramedPhysicalSquare.scalarTuple_point]
  cases right <;> simpa only [centerIndex,count,IntegralMixedFramedBankSnapshotBits.atKey,originalValues,
    Bool.false_eq_true,ite_false,ite_true] using HE

private theorem native_near_hom (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
    (hchild : pointProducer hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u))
    (hab : originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u))<
      originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u))) :
    NearHomModel hn ht ha hR0 right u hv :=by
  have HN:=HL.2.2.1
  simp only [IntegralMixedRoadmapProperRowWitness.query,nearLanguage,IntegralFramedPhysicalNear.guarded,
    Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] at HN
  obtain ⟨hmeta,hw,HA⟩:=HN
  have HF : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))≤
      (G).birth (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)):=by
    simpa only [parentKey,IntegralMixedFramedTerminalCoordinateHeadBits.Valid,
      IntegralMixedFramedCoordinateCoefficientSpaceBits.arity,IntegralMixedFramedBankSnapshotBits.atKey] using hmeta.2.1
  have HC:=row_count_positive hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u) hv
  have HB : creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)≤
      (G).birth (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)):=
    ((actual_birth hn ht ha hR0 false _ hv).trans (parentBirth_eq hn ht ha hR0 false _ HC)).symm.trans_le HF
  have HAnchor:=native_center_value hn ht ha hR0 right u hv HL hw HB hmeta.2.2.2.1
  have HBackend:=IntegralFramedPhysicalNear.exists_near_iff P BP BH BL BF BC BS
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false)
    (positive hn ht ha hR0 false) hf hd right
    (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u)
    hw hmeta.1 hmeta.2.1 hmeta.2.2.1 hmeta.2.2.2.1 hmeta.2.2.2.2
    (a:=originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u)))
    (b:=originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u))) hab HAnchor
    (Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u))
  obtain ⟨φ,hγ,HNearIff⟩:=HBackend
  have HCanon:=(IntegralFramedPhysicalNear.accept_rank_word P BP BH BL BF BC BS
    (parent hn ht ha hR0 false) (terminal hn ht ha hR0 false)
    (centerIndex hn ht ha hR0 right) (pointIndex hn ht ha hR0 false false)
    (positive hn ht ha hR0 false) hf hd right
    (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord false u)
    (IntegralMixedRoadmapProperRowWitness.rank u)).mp HA
  have HNear:=HNearIff.mp HCanon
  have HY:=native_scalar_value hn ht ha hR0 false right u hv HL hw _ hchild HB
  have HS : IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 false)
        (positive hn ht ha hR0 false) (IntegralMixedRoadmapProperRowWitness.key u)
        (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw)
      ⟨pointIndex hn ht ha hR0 false false (IntegralMixedRoadmapProperRowWitness.key u),hmeta.2.2.2.2⟩=
      originalValues hn ht ha hR0 u hv (pointProducer hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)):=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    simpa only [pointIndex,count,IntegralMixedFramedBankSnapshotBits.atKey,originalValues] using HY
  rw [HS] at HNear
  have HG : NativeInterprets hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)
      (IntegralMixedRoadmapProperRowWitness.ownWord false u) hw HF φ:=by
    simpa only [NativeInterprets,parentKey] using hγ
  have HOrig:=native_original_quotients hn ht ha hR0 right u hv HL
  unfold NativeOriginalModel at HOrig
  unfold NearHomModel
  refine ⟨hw,HF,φ,HG,HOrig hw HF φ HG,?_⟩
  have Hend : (if right then originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u))
      else originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u)))=
      originalValues hn ht ha hR0 u hv (oldProducer right (IntegralMixedRoadmapProperRowWitness.key u)):=by
    cases right <;> rfl
  simpa only [Hend,parentKey] using HNear

private def RankHomModel (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u)) : Prop:=
  ∃hw : SquareSampleCompleteVertices.Valid (Input (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true))
    (IntegralMixedRoadmapProperRowWitness.key u) (IntegralMixedRoadmapProperRowWitness.ownWord true u),
  ∃hfit : (G).birth (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))≤
    (G).birth (terminal hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)),
  ∃ψ : ((G).state (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    NativeInterprets hn ht ha hR0 true _ _ hw hfit ψ ∧
    let p:=(selected ((G).state (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))) ((G).birth_bound _)
      ((G).rule (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))
        (get P Field.slot13 (parent hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)))) ψ).map (evalRingHom 0)
    let y:=originalValues hn ht ha hR0 u hv (pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))
    y∈p.roots.toFinset ∧OrderedRealRootWindow.rank p.roots.toFinset y=Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u)

attribute [local irreducible] RankHomModel

private theorem native_rank_hom (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
    (hmid : pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)) :
    RankHomModel hn ht ha hR0 u hv :=by
  have HR:=HL.2.2.2.1
  simp only [IntegralMixedRoadmapProperRowWitness.query] at HR
  obtain ⟨hmeta,hw,HK⟩:=(rankLanguage_iff hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)
    (IntegralMixedRoadmapProperRowWitness.ownWord true u) (IntegralMixedRoadmapProperRowWitness.rank u)).mp HR
  unfold RankAt IntegralFramedZeroTarskiStatistic.RankAt at HK
  obtain ⟨ψ,hγ,HK⟩:=HK
  have HF : (G).birth (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))≤
      (G).birth (terminal hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)):=by
    simpa only [parentKey,IntegralMixedFramedTerminalCoordinateHeadBits.Valid,
      IntegralMixedFramedCoordinateCoefficientSpaceBits.arity,IntegralMixedFramedBankSnapshotBits.atKey] using hmeta.2.1
  have HC:=row_count_positive hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u) hv
  have HB : creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u)≤
      (G).birth (terminal hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)):=
    ((actual_birth hn ht ha hR0 true _ hv).trans (parentBirth_eq hn ht ha hR0 true _ HC)).symm.trans_le HF
  have HY:=native_scalar_value hn ht ha hR0 true right u hv HL hw _ hmid HB
  have HS : IntegralMixedCanonicalBankPoint.point
      (IntegralMixedFramedBankTermSign.state P BP BH (terminal hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)))
      (IntegralFramedPhysicalSquare.scalarTuple P BP BH BL BF BC BS (terminal hn ht ha hR0 true)
        (positive hn ht ha hR0 true) (IntegralMixedRoadmapProperRowWitness.key u)
        (IntegralMixedRoadmapProperRowWitness.ownWord true u) hw)
      ⟨pointIndex hn ht ha hR0 true true (IntegralMixedRoadmapProperRowWitness.key u),hmeta.2.2.2.2⟩=
      originalValues hn ht ha hR0 u hv (pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)):=by
    rw [IntegralFramedPhysicalSquare.scalarTuple_point]
    simpa only [pointIndex,count,IntegralMixedFramedBankSnapshotBits.atKey,originalValues] using HY
  dsimp only at HK
  rw [HS] at HK
  have HG : NativeInterprets hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)
      (IntegralMixedRoadmapProperRowWitness.ownWord true u) hw HF ψ:=by
    simpa only [NativeInterprets,parentKey] using hγ
  unfold RankHomModel
  exact ⟨hw,HF,ψ,HG,HK⟩

private theorem reverse_reference (a b p i : ℕ) (hab : a=b) (hp : p<b) (hi : i=b-1-p) :
    a-1-i=p :=by omega

private theorem mean_reference_value (side right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
    (φ : ((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (H : QuotientsAt G (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)) φ
      (originalValues hn ht ha hR0 u hv)) :
    φ (((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).bank.numerator
      (actualMeanReference hn ht ha hR0 side (IntegralMixedRoadmapProperRowWitness.key u) hv HL.1))/
      (((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))).bank.denominator
        (actualMeanReference hn ht ha hR0 side (IntegralMixedRoadmapProperRowWitness.key u) hv HL.1):ℝ)=
      originalValues hn ht ha hR0 u hv (oldProducer side (IntegralMixedRoadmapProperRowWitness.key u)) :=by
  have HG:=parent_good hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)
    (row_count_positive hn ht ha hR0 _ hv) HL.1
  have HP : oldProducer side (IntegralMixedRoadmapProperRowWitness.key u)<
      parentBirth hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u):=by
    cases side
    · exact HG.2.2.1
    · exact HG.2.2.2.1
  have HR : (actualMeanReference hn ht ha hR0 side (IntegralMixedRoadmapProperRowWitness.key u) hv HL.1).val=
      parentBirth hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)-1-
        oldProducer side (IntegralMixedRoadmapProperRowWitness.key u) :=by
    simp only [actualMeanReference,meanReference,IntegralMixedChronologicalMidpoint.reference,Fin.val_mk]
  have HI : (G).birth (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))-1-
      (actualMeanReference hn ht ha hR0 side (IntegralMixedRoadmapProperRowWitness.key u) hv HL.1).val=
      oldProducer side (IntegralMixedRoadmapProperRowWitness.key u) :=
    reverse_reference _ _ _ _ (actual_birth hn ht ha hR0 false _ hv) HP HR
  simpa only [HI] using H (actualMeanReference hn ht ha hR0 side (IntegralMixedRoadmapProperRowWitness.key u) hv HL.1)

private def CoordinateAt (right : Bool) (z : List Bool) (values : ℕ→ℝ) : Prop:=
  ∃φ : ((G).state (parentKey hn ht ha hR0 false z)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    QuotientsAt G (parentKey hn ht ha hR0 false z) φ
      values ∧
    IntegralMixedSelectedCoordinateEndpoint.Near
      ((G).state (parentKey hn ht ha hR0 false z)) ((G).birth_bound _)
      ((G).rule (parentKey hn ht ha hR0 false z)) φ
      (values (oldProducer false z))
      (values (oldProducer true z))
      (values (oldProducer right z))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey hn ht ha hR0 false z)
        (get P Field.slot13 (parent hn ht ha hR0 false z)))
      (IntegralMixedSelectedRootRank.rank
        ((G).state (parentKey hn ht ha hR0 false z)) ((G).birth_bound _)
        ((G).rule (parentKey hn ht ha hR0 false z)) φ
        ((values (oldProducer false z)+
          values (oldProducer true z))/2)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey hn ht ha hR0 false z)
          (get P Field.slot13 (parent hn ht ha hR0 false z)))
        (values (pointProducer hn ht ha hR0 true z)))
      (values (pointProducer hn ht ha hR0 false z))


attribute [local irreducible] CoordinateAt

private def CoordinateOutcome (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u)) : Prop:=
  CoordinateAt hn ht ha hR0 right (IntegralMixedRoadmapProperRowWitness.key u)
    (originalValues hn ht ha hR0 u hv)

attribute [local irreducible] CoordinateOutcome

private theorem native_coordinate_outcome (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u))
    (HL : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right)
    (hchild : pointProducer hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u))
    (hmid : pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u))
    (hab : originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u))<
      originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u))) :
    CoordinateOutcome hn ht ha hR0 right u hv :=by
  have HN:=native_near_hom hn ht ha hR0 right u hv HL hchild hab
  unfold NearHomModel at HN
  obtain ⟨hO,hFO,φ,hφ,HOriginal,HNear⟩:=HN
  have HM:=native_rank_hom hn ht ha hR0 right u hv HL hmid
  unfold RankHomModel at HM
  obtain ⟨hM,hFM,ψ,hψ,HMem,Hrank⟩:=HM
  have HCommon:=native_parent_quotients hn ht ha hR0 right u hv HL
  unfold NativeAgreementModel at HCommon
  have HAgree:=HCommon hO hM hFO hFM φ ψ hφ hψ
  let jo:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G
    (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))
    (get P Field.slot13 (parent hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)))
  let jm:=IntegralMixedCoordinateCoefficientSnapshot.coordinate G
    (parentKey hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))
    (get P Field.slot13 (parent hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)))
  have HJ : jo.val=jm.val:=(selected_coordinate hn ht ha hR0 false _ hv HL.1).trans
    (selected_coordinate hn ht ha hR0 true _ hv HL.1).symm
  have HRoots:=actual_mean_roots hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u) hv HL.1
  unfold MeanRootsModel at HRoots
  have HR:=HRoots φ ψ HAgree jo jm HJ
  rw [mean_reference_value hn ht ha hR0 false right u hv HL φ HOriginal,
    mean_reference_value hn ht ha hR0 true right u hv HL φ HOriginal] at HR
  rw [HR] at Hrank
  have HCode : Nat.fromBitsLE (IntegralMixedRoadmapProperRowWitness.rank u)=
      IntegralMixedSelectedRootRank.rank
        ((G).state (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))) ((G).birth_bound _)
        ((G).rule (parentKey hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u))) φ
        ((originalValues hn ht ha hR0 u hv (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u))+
          originalValues hn ht ha hR0 u hv (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u)))/2) jo
        (originalValues hn ht ha hR0 u hv (pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u))) :=by
    symm
    simpa only [IntegralMixedSelectedRootRank.rank,IntegralMixedFrozenFrameSectionCode.roots,
      IntegralMixedFrozenFrameSectionCode.polynomial,OrderedRealRootWindow.rank] using Hrank
  rw [HCode] at HNear
  unfold CoordinateOutcome CoordinateAt
  exact ⟨φ,HOriginal,HNear⟩

noncomputable def CoordinateMeaning (right : Bool) (q : List Bool) (j : ℕ)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) : Prop:=
  let z:=pair q (BinaryNatCode.encode j)
  let old:=parentKey hn ht ha hR0 false z
  IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z ∧
  IntegralMixedRoadmapProperRowWitness.SideGood right z ∧
  ∃φ : ((G).state old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀i,φ (((G).state old).bank.numerator i)/(((G).state old).bank.denominator i:ℝ)=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv ((G).birth old-1-i.val)) ∧
    IntegralMixedSelectedCoordinateEndpoint.Near ((G).state old) ((G).birth_bound old) ((G).rule old) φ
      (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
      (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))
      (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer right q))
      (IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent hn ht ha hR0 false z)))
      (IntegralMixedSelectedRootRank.rank ((G).state old) ((G).birth_bound old) ((G).rule old) φ
        ((IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)+
          IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))/2)
        (IntegralMixedCoordinateCoefficientSnapshot.coordinate G old (get P Field.slot13 (parent hn ht ha hR0 false z)))
        (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
          (IntegralMixedRoadmapProper.midProducer (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
            (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q j)))
      (IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv
        (IntegralMixedRoadmapProper.childProducer (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q j))

private theorem original_field_eq (a b : List Bool) (he : a=b)
    (hA : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 a)
    (hB : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 b) :
    originalValue hn ht ha hR0 a hA=IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 b hB :=by
  subst b
  rfl

theorem coordinate_meaning (right : Bool) (q : List Bool) (j : ℕ)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HB : IntegralMixedRoadmapProper.Base hn ht ha hR0 q)
    (hj : IntegralMixedRoadmapAtomic.depth q≤j)
    (hjn : j≤IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (H : IntegralMixedRoadmapProperCoordinateSearch.Holds hn ht ha hR0 right (pair q (BinaryNatCode.encode j))) :
    CoordinateMeaning hn ht ha hR0 right q j hv :=by
  obtain ⟨code,_,o,_,m,_,HL⟩:=H
  let u:=IntegralMixedRoadmapProperRowWitness.packet (pair q (BinaryNatCode.encode j)) o m code
  have HLU : u∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right:=HL
  have HK : IntegralMixedRoadmapProperRowWitness.key u=pair q (BinaryNatCode.encode j):=by
    simp only [u,IntegralMixedRoadmapProperRowWitness.packet,IntegralMixedRoadmapProperRowWitness.key,pairFst_pair]
  have HAtomic : IntegralMixedRoadmapProperRowWitness.atomic u=q:=by
    simp only [IntegralMixedRoadmapProperRowWitness.atomic,HK,atomic,pairFst_pair]
  have HV : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.atomic u):=by
    rw [HAtomic];exact hv
  have HC : pointProducer hn ht ha hR0 false (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    simpa only [HK,pointProducer,dimension,initial,atomic,coordinate,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,Bool.false_eq_true,ite_false] using
      IntegralMixedRoadmapProper.child_producer_before_probe hn ht ha hR0 q hv j hj hjn
  have HM : pointProducer hn ht ha hR0 true (IntegralMixedRoadmapProperRowWitness.key u)<
      creating hn ht ha hR0 (IntegralMixedRoadmapProperRowWitness.key u):=by
    simpa only [HK,pointProducer,dimension,initial,atomic,coordinate,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits,ite_true] using
      IntegralMixedRoadmapProper.mid_producer_before_probe hn ht ha hR0 q hv HB.1 j hj hjn
  have HA : originalValues hn ht ha hR0 u HV (oldProducer false (IntegralMixedRoadmapProperRowWitness.key u))<
      originalValues hn ht ha hR0 u HV (oldProducer true (IntegralMixedRoadmapProperRowWitness.key u)):=by
    simpa only [originalValues,originalValue,HAtomic,HK,oldProducer,atomic,pairFst_pair,
      IntegralMixedRoadmapLocalFrame.field] using IntegralMixedRoadmapLocalFrame.order_of_base hn ht ha hR0 q hv HB
  have HO:=native_coordinate_outcome hn ht ha hR0 right u HV HLU HC HM HA
  unfold CoordinateOutcome at HO
  rw [HK] at HO
  have HVals : originalValues hn ht ha hR0 u HV=
      IntegralMixedRoadmapLocalFrame.field hn ht ha hR0 q hv :=by
    unfold originalValues
    exact original_field_eq hn ht ha hR0 _ _ HAtomic HV hv
  rw [HVals] at HO
  unfold CoordinateAt at HO
  simp only [QuotientsAt,oldProducer,pointProducer,dimension,initial,
    atomic,coordinate,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,
    Bool.false_eq_true,ite_false,ite_true] at HO
  unfold CoordinateMeaning
  refine ⟨?_,?_,?_⟩
  · simpa only [HK] using HLU.1
  · simpa only [HK] using HLU.2.1
  · exact HO

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow
