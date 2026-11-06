/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalPreparedPrefix
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry
public import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentCritical
/-! # The original provider point supplies a nonempty coarse critical slice -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B

noncomputable def originalAmbient (q : List Bool) :=
  (P).ambient (pairFst ((B).key (FormulaSignSlotRadialProviderAtomic.context q)))

theorem original_point_good (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    IntegralMixedChronologicalFrameCode.PointGood (originalAmbient q) (originalBirth q)
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.levelIndex q)
      (IntegralMixedRoadmapProper.levelIndex q) :=by
  have HG:=coarse_point_good q [] hv hd
  rw [query_dimension,query_birth q [] (count_positive q hv)] at HG
  change IntegralMixedChronologicalFrameCode.PointGood (FormulaSignSlotRadialProviderAtomic.dimension q)
    (originalBirth q) _ _ _ at HG
  rw [←FormulaSignSlotRadialProviderAtomic.native_dimension q] at HG
  exact HG

noncomputable def originalDescriptor (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :=
  IntegralMixedChronologicalFrameCode.descriptor (originalAmbient q) (originalBirth q)
    (IntegralMixedRoadmapProper.labels q) (original_point_good q hv hd).1
noncomputable def originalValues (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (i : Fin (originalBirth q)) : ℝ := originalNaturalValues q hv i.val
noncomputable def originalHeight (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) : Fin (originalAmbient q+1) :=
  ⟨IntegralMixedRoadmapProper.levelIndex q,(original_point_good q hv hd).2.2.1⟩
noncomputable def originalCriticalValues (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) : Set ℝ :=
  realCriticalValues (FormulaSignSlotRadialProviderAtomic.source q)
    (line (originalDescriptor q hv hd).frame (originalHeight q hv hd)) (originalValues q hv) (originalHeight q hv hd)
noncomputable def OriginalSliceCriticalFree (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) : Prop :=
  Disjoint (Ioo (originalField q hv (IntegralMixedRoadmapProper.producer false q))
    (originalField q hv (IntegralMixedRoadmapProper.producer true q))) (originalCriticalValues q hv hd)

private theorem proper_heq {a b : ℕ} (Q : SpatialSource a) (R : SpatialSource b)
    (hn : a=b) (he : HEq Q R)
    (hR : IsProperMap (fun x : Fin (b+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial R.low R.leading R.degree).eval₂ (Int.castRingHom ℝ) x)) :
    IsProperMap (fun x : Fin (a+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial Q.low Q.leading Q.degree).eval₂ (Int.castRingHom ℝ) x) :=by
  cases hn
  have HQ : Q=R:=eq_of_heq he
  cases HQ
  exact hR

theorem original_source_proper (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    IsProperMap (fun x : Fin (originalAmbient q+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial (FormulaSignSlotRadialProviderAtomic.source q).low
        (FormulaSignSlotRadialProviderAtomic.source q).leading
        (FormulaSignSlotRadialProviderAtomic.source q).degree).eval₂ (Int.castRingHom ℝ) x) :=by
  apply proper_heq _ (FormulaSignSlotRadialProviderIntegerPlan.spatial (FormulaSignSlotRadialProviderAtomic.provider q))
    ((FormulaSignSlotRadialProviderAtomic.native_dimension q).trans (FormulaSignSlotRadialProviderAtomic.dimension_provider q))
    (FormulaSignSlotRadialProviderAtomic.source_provider q hv)
  exact FormulaSignSlotRadialProviderMarkedGeometry.proper (FormulaSignSlotRadialProviderAtomic.provider q)

private theorem levels_original (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (i : ℕ) (hi : i<FormulaSignSlotRadialProviderAtomic.depth q) :
    FormulaSignSlotRadialProviderAtomic.levels q hv i=originalField q hv
      (Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i)) :=by
  have HL:= (FormulaSignSlotRadialProviderAtomic.own_frame_good q hv).2 i
    (by rw [FormulaSignSlotRadialProviderAtomic.frozen_count];exact hi)
  have HA:= (IntegralFramedPhysicalCompanionPoint.active_direct B FormulaSignSlotRadialProviderRecordPlan.tables
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.ownBirth q)
    (FormulaSignSlotRadialProviderAtomic.own_active q hv)).1
  have HB : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i)<
      FormulaSignSlotRadialProviderFieldEquality.count (FormulaSignSlotRadialProviderAtomic.context q) :=
    HL.trans (HA.trans_eq (IntegralMixedFramedHistoryFamilyBits.family_birth
      (B).parameters (B).plan (B).data ((B).key (FormulaSignSlotRadialProviderAtomic.context q))).symm)
  have HE:=FormulaSignSlotRadialProviderFieldEquality.point_env
    (FormulaSignSlotRadialProviderAtomic.context q) (FormulaSignSlotRadialProviderAtomic.word q)
    (FormulaSignSlotRadialProviderAtomic.full_valid q hv) _ HB
  exact HE.symm

private theorem descriptor_label_lookup {n m : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n m)
    (i : Fin d.labels.length) :
    Nat.fromBitsLE (WordList.get (IntegralMixedChronologicalFrameCode.labels d) i.val)=(d.labels[i]).val :=by
  simpa only [List.get_eq_getElem,Fin.getElem_fin] using
    IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt

theorem original_labels_length (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    (originalDescriptor q hv hd).labels.length=IntegralMixedRoadmapProper.levelIndex q :=by
  unfold originalDescriptor
  rw [IntegralMixedChronologicalFrameCode.descriptor_length,IntegralMixedRoadmapProper.labels_count]

theorem original_descriptor_lookup (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (i : ℕ)
    (hi : i<WordListRecords.count (IntegralMixedRoadmapProper.labels q)) :
    Nat.fromBitsLE (WordList.get (IntegralMixedChronologicalFrameCode.labels (originalDescriptor q hv hd)) i)=
      Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i) :=by
  unfold originalDescriptor
  exact IntegralMixedChronologicalFrameCode.descriptor_lookup (originalAmbient q) (originalBirth q)
    (IntegralMixedRoadmapProper.labels q) (original_point_good q hv hd).1 i hi

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  originalDescriptor originalBirth originalField IntegralMixedRoadmapProper.labels
  FormulaSignSlotRadialProviderAtomic.source FormulaSignSlotRadialProviderAtomic.point
  FormulaSignSlotRadialProviderAtomic.levels

theorem original_slice_nonempty (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    (slice (FormulaSignSlotRadialProviderAtomic.source q)
      (originalDescriptor q hv hd).frame (originalValues q hv)).Nonempty :=by
  let p:=FormulaSignSlotRadialProviderAtomic.point q hv
  have HP:=FormulaSignSlotRadialProviderAtomic.occurrence q hv
  let d:=originalDescriptor q hv hd
  refine ⟨p,(d.slice_iff _ _ p).mpr ⟨HP.zero,?_⟩⟩
  intro i
  have HL : d.labels.length=IntegralMixedRoadmapProper.levelIndex q:=by
    exact original_labels_length q hv hd
  have HI : i.val<IntegralMixedRoadmapProper.levelIndex q:=i.isLt.trans_eq HL
  have HDepth : i.val<FormulaSignSlotRadialProviderAtomic.depth q:=by
    change i.val<FormulaSignSlotRadialProviderAtomic.depth q-1 at HI
    omega
  have HFrozen:=HP.frozen ⟨i.val,lt_of_lt_of_le i.isLt d.length_le⟩ HDepth
  have HLabels : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val)=
      (d.labels[i]).val:=by
    have HE : Nat.fromBitsLE (WordList.get (IntegralMixedChronologicalFrameCode.labels d) i.val)=
        (d.labels[i]).val:=by
      exact descriptor_label_lookup d i
    have HD : Nat.fromBitsLE (WordList.get (IntegralMixedChronologicalFrameCode.labels d) i.val)=
        Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i.val):=
      original_descriptor_lookup q hv hd i.val
        (by rw [IntegralMixedRoadmapProper.labels_count];exact HI)
    have HF : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen q) i.val)=
        Nat.fromBitsLE (WordList.get (IntegralMixedRoadmapProper.labels q) i.val):=by
      simpa only [FormulaSignSlotRadialProviderAtomic.frozen,IntegralMixedRoadmapProper.labels,
        IntegralMixedRoadmapAtomic.payload,FormulaSignSlotRadialProviderAtomic.payload] using
        (IntegralMixedRoadmapChain.frozen_lookup (FormulaSignSlotRadialProviderAtomic.payload q)
        (FormulaSignSlotRadialProviderAtomic.depth q) i.val HDepth).trans
          (IntegralMixedRoadmapChain.frozen_lookup (FormulaSignSlotRadialProviderAtomic.payload q)
            (IntegralMixedRoadmapProper.levelIndex q) i.val HI).symm
    exact HF.trans (HD.symm.trans HE)
  have HReverse : originalBirth q-1-(d.reference i).val=(d.labels[i]).val:=by
    have HB:=(d.labels[i]).isLt
    simp only [IntegralMixedChronologicalFrame.Descriptor.reference,Fin.val_mk]
    omega
  change p _=originalField q hv (originalBirth q-1-(d.reference i).val)
  rw [HReverse,←HLabels]
  exact HFrozen.trans (levels_original q hv i.val HDepth)

theorem original_critical_nonempty (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) :
    (originalCriticalValues q hv hd).Nonempty :=by
  obtain ⟨p,hp⟩:=original_slice_nonempty q hv hd
  let d:=originalDescriptor q hv hd
  let h:=originalHeight q hv hd
  have HH : h∉d.frame.frozen:=by
    rw [d.frozen_mem]
    have HL : d.labels.length=IntegralMixedRoadmapProper.levelIndex q:=by
      exact original_labels_length q hv hd
    rw [HL]
    exact Nat.lt_irrefl _
  obtain ⟨y,HY,HG⟩:=exists_component_critical_of_proper
    (FormulaSignSlotRadialProviderAtomic.source q)
    d.frame (originalValues q hv) h HH
    (original_source_proper q hv) p hp
  refine ⟨y h,?_⟩
  exact (line_realCriticalValues_iff _ d.frame _ h HH d.free_normal _).mpr
    ⟨y,connectedComponentIn_subset _ _ HY,rfl,HG⟩


end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
