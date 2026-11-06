/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraphGeometry
public import LeanCanny.Geometry.IntegralMixedFrozenFrameTerminal
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendIdentity
/-! # Actual provider terminal fibers are finite -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open IntegralMixedHistory IntegralMixedFrozenFrame IntegralCriticalHistoryTask Set
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem provider_finite_reference_fiber {dim sched bits born :ℕ} {Q :SpatialSource dim}
    {ι :Type} (x :State Q sched bits born ι) (hm :born≤sched)
    (phi :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values :Fin born→ℝ)
    (HV :∀i,phi (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (refs :Fin dim→Fin born) (levels :ℕ→ℝ) (HL :∀i,values (refs i)=levels i.val) :
    Set.Finite {y :Fin (dim+1)→ℝ |
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
      ∀i :Fin (dim+1),i.val<dim→y i=levels i.val}:=by
  let frame :Frame dim:={
    frozen:=Finset.univ.filter (fun i=>i.val<dim)
    scales:=fun _=>1
    scales_ne_zero:=fun _=>by norm_num
    heights:=fun i=>if hi :i.val<dim then .reference (refs ⟨i.val,hi⟩).val else .constant 0 }
  have HH :Fin.last dim∉frame.frozen:=by simp [frame]
  have HF (i :Fin (dim+1)) (hi :i≠Fin.last dim) :i∈frame.frozen:=by
    have HE :i.val≠dim:=by intro h;apply hi;exact Fin.ext h
    simp only [frame,Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  let :Finite (slice Q frame values):=(last_free_finite_card x hm phi frame (Fin.last dim) HH HF values HV).1
  apply (Set.toFinite (slice Q frame values)).subset
  intro y hy
  refine ⟨hy.1,?_⟩
  intro i hi
  have HI :i.val<dim:=by simpa only [frame,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have HE :(frame.heights i).evaluate values=values (refs ⟨i.val,HI⟩):=by
    simp only [frame,dite_eq_left HI,AffineExpr.evaluate,dite_eq_left (refs ⟨i.val,HI⟩).isLt]
  have HS :(frame.scales i:ℝ)=1:=by simp only [frame,Int.cast_one]
  rw [HS,one_mul,HE]
  exact (hy.2 i HI).trans (HL ⟨i.val,HI⟩).symm

private theorem provider_finite_source_transport {a b :ℕ} (Q :SpatialSource a) (R :SpatialSource b)
    (HD :a=b) (HS :HEq Q R) (levels :ℕ→ℝ)
    (HF :Set.Finite {y :Fin (a+1)→ℝ |
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
      ∀i :Fin (a+1),i.val<a→y i=levels i.val}) :
    Set.Finite {y :Fin (b+1)→ℝ |
      (FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) y=0 ∧
      ∀i :Fin (b+1),i.val<b→y i=levels i.val}:=by
  cases HD
  cases eq_of_heq HS
  exact HF

private theorem provider_source_at_heq {n : List Bool→ℕ} (F : (c : List Bool)→SpatialSource (n c))
    (a b : List Bool) (h : a=b) : HEq (F a) (F b) := by cases h;rfl

private theorem provider_family_ambient (a : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (h : IntegralMixedFramedHistoryFamilyBits.Data a d) (k : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family a d h).ambient k=a.ambient (pairFst k) := rfl

private theorem provider_family_source (a : Parameters) (d : IntegralMixedFramedHistoryFamilyBits.Plan a)
    (h : IntegralMixedFramedHistoryFamilyBits.Data a d) (k : List Bool) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family a d h).spatial k)
      (IntegralMixedFramedHistoryFamilyBits.instruction a d k).source :=
  heq_of_eq (IntegralMixedFramedHistoryFamilyBits.family_spatial a d h k)

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

private theorem provider_certified_source (key : List Bool) :
    HEq (IntegralMixedFramedHistoryFamilyBits.instruction
      FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
      FormulaSignSlotRadialProviderRecordPlan.certifiedPlan key).source
      (FormulaSignSlotRadialProviderRecordPlan.spatial (pairFst key)) := by
  have HI := IntegralMixedFramedNormalizationBits.planned_instruction
    FormulaSignSlotRadialProviderRecordPlan.parameters FormulaSignSlotRadialProviderRecordPlan.plan
    (fun _=>3) FormulaSignSlotRadialProviderRecordPlan.factor FormulaSignSlotRadialProviderRecordPlan.seed key
  have HS := congrArg (fun I : IntegralMixedFramedHistoryScript.Instruction
    (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (pairFst key))
    (FormulaSignSlotRadialProviderRecordPlan.parameters.width (pairFst key))=>I.source) HI
  exact heq_of_eq (HS.trans (FormulaSignSlotRadialProviderRecordPlan.instruction_source key))

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "num" => FormulaSignSlotRadialProviderMarkedGeometry.number

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

theorem full_bank_source (q : List Bool) :
    HEq ((G).spatial ((B).key (FormulaSignSlotRadialProviderAtomic.context q)))
      (FormulaSignSlotRadialProviderAtomicGeometry.source (FormulaSignSlotRadialProviderAtomic.provider q)) := by
  have HE := (provider_family_source P D H
    ((B).key (FormulaSignSlotRadialProviderAtomic.context q))).trans (provider_certified_source _)
  have HR := provider_source_at_heq FormulaSignSlotRadialProviderRecordPlan.spatial _ _
    (FormulaSignSlotRadialProviderAtomic.context_root q)
  exact HE.trans (HR.trans ((FormulaSignSlotRadialProviderAtomic.spatial_provider q).trans
    (FormulaSignSlotRadialProviderAtomicGeometry.source_heq _).symm))

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderAtomic.levels FormulaSignSlotRadialProviderAtomic.point

theorem terminal_label_bound (q : List Bool) (hv : A q)
    (ht : FormulaSignSlotRadialProviderAtomic.depth q=FormulaSignSlotRadialProviderAtomic.dimension q)
    (i : Fin ((P).ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q))))) :
    Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val)<
      IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (FormulaSignSlotRadialProviderAtomic.context q)) := by
  have HI : i.val<WordListRecords.count (FormulaSignSlotRadialProviderAtomic.frozen q) := by
    rw [FormulaSignSlotRadialProviderAtomic.frozen_count,ht,
      ←FormulaSignSlotRadialProviderAtomic.native_dimension q]
    exact i.isLt
  have HB := (FormulaSignSlotRadialProviderAtomic.own_frame_good q hv).2 i.val HI
  have HA := (IntegralFramedPhysicalCompanionPoint.active_direct B T
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.ownBirth q)
      (FormulaSignSlotRadialProviderAtomic.own_active q hv)).1
  exact HB.trans HA

noncomputable def frozenSlice (c : List Bool) (k : ℕ) (levels : ℕ→ℝ) : Set (Fin (num c+4)→ℝ) :=
  FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c∩{p |∀i : Fin (num c+4),i.val<k→p i=levels i.val}

theorem terminal_provider_fiber_finite (q : List Bool) (hv : A q)
    (ht : FormulaSignSlotRadialProviderAtomic.depth q=FormulaSignSlotRadialProviderAtomic.dimension q) :
    Set.Finite (frozenSlice (FormulaSignSlotRadialProviderAtomic.provider q)
      (num (FormulaSignSlotRadialProviderAtomic.provider q)+3) (FormulaSignSlotRadialProviderAtomic.levels q hv)) := by
  let ctx := FormulaSignSlotRadialProviderAtomic.context q
  let key := (B).key ctx
  let word := FormulaSignSlotRadialProviderAtomic.word q
  have hw := FormulaSignSlotRadialProviderAtomic.full_valid q hv
  let values := IntegralFramedPhysicalSquare.point P D H (B).nodes (B).factor (B).seed
    (B).bounds (B).key (B).positive ctx word hw
  have HInterpret := IntegralFramedPhysicalSquare.exists_interpretation P D H
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive ctx word hw
  let phi := HInterpret.choose
  have HV := HInterpret.choose_spec.2
  let refs : Fin ((P).ambient (pairFst key))→Fin ((G).birth key) := fun i=>
    ⟨IntegralMixedFramedHistoryFamilyBits.prefixLength P key-1-
      Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val),by
        rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
        have HL := terminal_label_bound q hv ht i
        change Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val)<
          IntegralMixedFramedHistoryFamilyBits.prefixLength P key at HL
        omega⟩
  have HL (i : Fin ((P).ambient (pairFst key))) :
      values (refs i)=FormulaSignSlotRadialProviderAtomic.levels q hv i.val := by
    have HI : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val)<
        (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count := by
      change _<(G).birth key
      rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
      exact terminal_label_bound q hv ht i
    have HE := IntegralFramedPhysicalBankTerm.env_chronological B T
      FormulaSignSlotRadialProviderAtomic.bank_represents ctx word hw _ HI
    simpa only [FormulaSignSlotRadialProviderAtomic.levels,FormulaSignSlotRadialProviderAtomic.field,
      FormulaSignSlotRadialProviderAtomic.bankField,values,refs,
      IntegralMixedFramedHistoryFamilyBits.family_birth,ctx,word] using HE.symm
  have HA : (G).ambient key=(P).ambient (pairFst key) := provider_family_ambient P D H key
  let refs' : Fin ((G).ambient key)→Fin ((G).birth key) := fun i=>refs (Fin.cast HA i)
  have HL' (i : Fin ((G).ambient key)) : values (refs' i)=FormulaSignSlotRadialProviderAtomic.levels q hv i.val :=
    HL (Fin.cast HA i)
  have HF := provider_finite_reference_fiber ((G).state key) ((G).birth_bound key)
    phi values HV refs' (FormulaSignSlotRadialProviderAtomic.levels q hv) HL'
  have HD := HA.trans (FormulaSignSlotRadialProviderAtomicGeometry.dimension_provider q)
  have HP := provider_finite_source_transport _ _ HD
    (full_bank_source q) (FormulaSignSlotRadialProviderAtomic.levels q hv) HF
  simpa only [frozenSlice,FormulaSignSlotRadialProviderAtomicGeometry.source,
    FormulaSignSlotRadialProviderMarkedGeometry.zeroSet,FormulaSignSlotRadialProviderMarkedGeometry.polynomial,
    Set.inter_def,Set.mem_ofPred_eq] using HP

theorem pointAt_frozenSlice (c q : List Bool) (hv : A q)
    (hc : FormulaSignSlotRadialProviderAtomic.provider q=c) :
    pointAt c q hv hc∈frozenSlice c (FormulaSignSlotRadialProviderAtomic.depth q)
      (FormulaSignSlotRadialProviderAtomic.levels q hv) :=
  ⟨pointAt_zero c q hv hc,(pointAt_occurrence c q hv hc).frozen⟩

private theorem provider_finite_joined_eq {α : Type*} [TopologicalSpace α] [T2Space α]
    (s : Set α) (HF : s.Finite) (x y : α) (HP : JoinedIn s x y) : x=y := by
  let : Finite s := HF.to_subtype
  let : TotallyDisconnectedSpace s := inferInstance
  have HE : (⟨x,HP.source_mem⟩ : s)=⟨y,HP.target_mem⟩ :=
    isPreconnected_connectedComponent.subsingleton mem_connectedComponent
      (pathComponent_subset_component _ HP.joined_subtype)
  exact congrArg Subtype.val HE

theorem terminal_pointAt_eq_of_joined (c old : List Bool) (hv : A old)
    (hc : FormulaSignSlotRadialProviderAtomic.provider old=c)
    (ht : FormulaSignSlotRadialProviderAtomic.depth old=num c+3)
    (target : Fin (num c+4)→ℝ)
    (HP : JoinedIn (frozenSlice c (num c+3) (FormulaSignSlotRadialProviderAtomic.levels old hv))
      (pointAt c old hv hc) target) : pointAt c old hv hc=target := by
  have HD : FormulaSignSlotRadialProviderAtomic.dimension old=num c+3 := by
    simpa only [hc] using (FormulaSignSlotRadialProviderAtomic.native_dimension old).symm.trans
      (FormulaSignSlotRadialProviderAtomicGeometry.dimension_provider old)
  have HF : Set.Finite (frozenSlice c (num c+3) (FormulaSignSlotRadialProviderAtomic.levels old hv)) := by
    subst c
    exact terminal_provider_fiber_finite old hv (ht.trans HD.symm)
  exact provider_finite_joined_eq _ HF _ _ HP

theorem terminal_fiber_glue (c a b : List Bool) (ha : A a) (hb : A b)
    (hca : FormulaSignSlotRadialProviderAtomic.provider a=c)
    (hcb : FormulaSignSlotRadialProviderAtomic.provider b=c)
    (ht : FormulaSignSlotRadialProviderAtomic.depth a=num c+3)
    (HP : JoinedIn (frozenSlice c (num c+3) (FormulaSignSlotRadialProviderAtomic.levels a ha))
      (pointAt c a ha hca) (pointAt c b hb hcb)) :
    LeanCanny.pair a b∈FormulaSignSlotRadialProviderIdentity.language ∧ RawReachable c a b := by
  have HE := terminal_pointAt_eq_of_joined c a ha hca ht (pointAt c b hb hcb) HP
  have HN : HEq (FormulaSignSlotRadialProviderAtomic.point a ha) (FormulaSignSlotRadialProviderAtomic.point b hb) :=
    (native_pointAt_heq c a ha hca).trans ((heq_of_eq HE).trans (native_pointAt_heq c b hb hcb).symm)
  have HI := FormulaSignSlotRadialProviderRetainedAppend.identity_of_atomic_point_heq a b ha hb
    (hca.trans hcb.symm) HN
  exact ⟨HI,ha,hb,hca,hcb,Relation.ReflTransGen.single (Or.inl HI)⟩

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderGraph
