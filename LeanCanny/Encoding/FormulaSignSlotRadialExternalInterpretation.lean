/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalSlackSource
public import LeanCanny.Algebra.IntegralMixedFramedFamilyRunView
public import LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRootsAt
/-! # One own external tuple interprets the actual certified slack algebra -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalInterpretation
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (Plan)
open FormulaSignSlotRadialExternalPreludeNative
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Values {n S B m : ℕ} {Q : SpatialSource n} {ι : Type} (x : State Q S B m ι) (v : ℕ → ℝ) : Prop :=
  ∃ φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
    ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i : ℝ)=v i.val

private theorem values_of_realizes {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (v : ℕ → ℝ) (h : IntegralMixedIntegerRealization.Realizes x v) : Values x v := by
  obtain ⟨_,φ,_,_,hv⟩ := h
  exact ⟨φ,hv⟩
private theorem values_reframe {n n' S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (R : SpatialSource n')
    (hR : PurePowerReductionBounds.dimension (n'+1) R.degree≤2^B) (v : ℕ → ℝ) :
    Values (reframe x R hR) v ↔ Values x v := Iff.rfl
private theorem values_heq {n S B m S' B' m' : ℕ} {Q : SpatialSource n} {ι κ : Type}
    (x : State Q S B m ι) (y : State Q S' B' m' κ) (v : ℕ → ℝ)
    (hS : S=S') (hB : B=B') (hm : m=m') (hi : ι=κ) (hxy : HEq x y) : Values x v ↔ Values y v := by
  cases hS
  cases hB
  cases hm
  cases hi
  cases eq_of_heq hxy
  rfl

private theorem full_values (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (root : List Bool) (N : ℕ) (hN : (D.rules root).length=N) (v : ℕ → ℝ)
    (hr : IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedHistoryScript.run (IntegralMixedFramedHistoryFamilyBits.initial P D root) (D.rules root)
        (by have HC := D.room root; omega)) v) :
    Values ((IntegralMixedFramedHistoryFamilyBits.family P D H).state
      (IntegralMixedFramedHistoryFamilyBits.keyAt root N [])) v := by
  cases hN
  let key := IntegralMixedFramedHistoryFamilyBits.keyAt root (D.rules root).length []
  let R := D.initialSource root
  have hc : (D.rules root).length≤P.cap root+1 := by have HC := D.room root; omega
  have hcs : (D.rules root).length≤P.cap root+1+1 := by omega
  have hroot : pairFst key=root := pairFst_pair _ _
  have hR : PurePowerReductionBounds.dimension (P.ambient root+1) R.degree≤2^P.width root :=
    (IntegralMixedFramedHistoryFamilyBits.initial P D root).critical_cap
  have hRkey : PurePowerReductionBounds.dimension (P.ambient root+1) R.degree≤2^P.width (pairFst key) := by
    rw [hroot]
    exact hR
  have he := IntegralMixedFramedFamilyRunView.stateView_reframe_full P D H root [] hc hcs R hRkey hR
  have hS : P.cap (pairFst key)+1=P.cap root+1 := congrArg (fun r => P.cap r+1) hroot
  have hB : P.width (pairFst key)=P.width root := congrArg P.width hroot
  have hm : (IntegralMixedFramedHistoryFamilyBits.commands P D key).length=(D.rules root).length :=
    (IntegralMixedFramedHistoryFamilyBits.family_birth P D H key).trans
      (IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P root _ [] hc)
  have hi := IntegralMixedFramedFamilyRunView.commands_index_full P D root [] hc
  have hv := (values_reframe _ R hR v).mpr (values_of_realizes _ v hr)
  exact (values_reframe _ R hRkey v).mp ((values_heq _ _ v hS hB hm hi he).mpr hv)

private theorem planned_values (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) (v : ℕ → ℝ) :
    Values ((IntegralMixedFramedHistoryFamilyBits.family
      (IntegralMixedFramedNormalizationBits.planned P L F C) (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C)).state key) v ↔
        Values ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) v := Iff.rfl

private theorem plan_length (P : Parameters) (Q : ∀r,SpatialSource (P.ambient r))
    (hdegree : ∀r,(Q r).degree=P.degree r)
    (hcap : ∀r,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient r+1) (P.degree r)≤2^P.width r)
    (T : IntegerPolynomialRootQueriesBits.Source) (N : List Bool → ℕ)
    (hz : ∀q,T.polynomial q≠0) (hd : ∀r i,T.degree (pair r (BinaryNatCode.encode i))≤2^P.width r)
    (hroom : ∀r,N r+2≤P.cap r+1) (r : List Bool) :
    ((IntegralMixedSourceIntegerPrelude.plan P Q hdegree hcap T N hz hd hroom).rules r).length=N r := List.length_ofFn

noncomputable def state (ctx : List Bool) :=
  (IntegralMixedFramedHistoryFamilyBits.family certifiedParameters certifiedPlan certifiedData).state
    (FormulaSignSlotRadialExternalSlackSource.key ctx)
attribute [local irreducible] FormulaSignSlotRadialExternalPrelude.spatial
  FormulaSignSlotRadialExternalCoordinates.source

private theorem rules_length (ctx : List Bool) :
    (FormulaSignSlotRadialExternalPrelude.plan.rules ctx).length=FormulaSignSlotRadialExternalPrelude.count ctx := by
  unfold FormulaSignSlotRadialExternalPrelude.plan
  exact plan_length FormulaSignSlotRadialExternalPrelude.parameters FormulaSignSlotRadialExternalPrelude.spatial
    FormulaSignSlotRadialExternalPrelude.spatial_degree FormulaSignSlotRadialExternalPrelude.source_cap
    FormulaSignSlotRadialExternalPrelude.source FormulaSignSlotRadialExternalPrelude.count
    FormulaSignSlotRadialExternalPrelude.source_nonzero FormulaSignSlotRadialExternalPrelude.source_degree_cap
    FormulaSignSlotRadialExternalPrelude.room ctx

theorem exists_quotients (ctx : List Bool) (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx) :
    Values (state ctx)
      (fun i =>
          FormulaSignSlotRadialExternalCoordinates.values ctx hw (FormulaSignSlotRadialExternalPrelude.count ctx-1-i)) := by
  have hr := FormulaSignSlotRadialExternalPrelude.realizes ctx hw
  have hv := full_values FormulaSignSlotRadialExternalPrelude.parameters FormulaSignSlotRadialExternalPrelude.plan
    FormulaSignSlotRadialExternalPrelude.data ctx _ (rules_length ctx) _ hr
  unfold state
  exact (planned_values FormulaSignSlotRadialExternalPrelude.parameters FormulaSignSlotRadialExternalPrelude.plan
    FormulaSignSlotRadialExternalPrelude.data (fun _=>1) (fun _=>1) seed
      (FormulaSignSlotRadialExternalSlackSource.key ctx) _).mpr hv

private theorem cleared_value {n S B m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S B m ι) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (i : Fin m) :
    φ (cleared x i)=(commonDenominator x : ℝ)*(φ (x.bank.numerator i)/(x.bank.denominator i : ℝ)) := by
  have HQ : (commonDenominator x : ℝ)≠0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  have HR := CommonIntegerDenominator.recover φ.toRingHom Finset.univ x.bank.denominator x.bank.numerator
    (fun j _ => x.denominator_ne_zero j) i (Finset.mem_univ _)
  exact ((mul_comm _ _).trans ((div_eq_iff HQ).mp HR).symm).symm

def CoordinateInterpretation (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (N : ℕ) (p : ℕ → ℝ) : Prop :=
  ∃ φ : ((IntegralMixedFramedClearedMatrixBits.family P D H).state key).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ,
    ∀ i : Fin N, φ (IntegralMixedFramedSlackMatrixBits.elementAt P D H key (N-i.val))=
      (IntegralMixedFramedSlackMatrixBits.commonAt P D H key : ℝ)*p i.val

private theorem interpretation_of_values (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (N : ℕ) (p v : ℕ → ℝ)
    (hv : Values ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) v)
    (ha : IntegralMixedFramedClearedMatrixBits.Active P key)
    (hb : (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key=N+1)
    (hp : ∀i : Fin N,v (N-i.val)=p i.val) : CoordinateInterpretation P D H key N p := by
  obtain ⟨φ,hφ⟩ := hv
  refine ⟨φ,fun i => ?_⟩
  have hi : N-i.val<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth key := by rw [hb]; omega
  rw [IntegralMixedFramedSlackMatrixBits.elementAt,ite_eq_left ha,dite_eq_left hi,cleared_value,hφ,hp]
  rfl

theorem exists_interpretation (ctx : List Bool) (hw : FormulaSignSlotRadialExternalCoordinates.OwnValid ctx) :
    CoordinateInterpretation certifiedParameters certifiedPlan certifiedData
      (FormulaSignSlotRadialExternalSlackSource.key ctx) (FormulaSignSlotRadialExternalPrelude.number ctx)
      (FormulaSignSlotRadialExternalCoordinates.point ctx hw) := by
  apply interpretation_of_values certifiedParameters certifiedPlan certifiedData
    (FormulaSignSlotRadialExternalSlackSource.key ctx) _ _ _ (exists_quotients ctx hw)
    (FormulaSignSlotRadialExternalSlackSource.active ctx)
    (FormulaSignSlotRadialExternalSlackSource.birth ctx)
  intro i
  have he : FormulaSignSlotRadialExternalPrelude.count ctx-1-(FormulaSignSlotRadialExternalPrelude.number ctx-i.val)=i.val := by
    have H := i.isLt
    unfold FormulaSignSlotRadialExternalPrelude.count
    omega
  simp only [he,FormulaSignSlotRadialExternalCoordinates.values,ite_eq_left i.isLt]

end LeanCanny.Encoding.FormulaSignSlotRadialExternalInterpretation
