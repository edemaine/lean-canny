/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalEndpointLabels
/-! # Appended endpoint labels are the exact original frozen child frame -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalEndpointCode
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedFullHistoryScript
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedCriticalRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}
open IntegralMixedChronologicalFrameCode (labels labels_count labels_lookup)

theorem append_actual (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) : appendLabels (labels d) a.val=labels (d.freeze a hk) :=by
  change WordList.encode ((List.range (WordListRecords.count (labels d)+1)).map (entry (labels d) a.val))=
    WordList.encode ((d.labels++[a]).map (fun i=>BinaryNatCode.encode i.val))
  rw [labels_count]
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_append,List.length_singleton]
  · intro i hi hj
    simp only [List.length_map,List.length_range] at hi
    simp only [List.getElem_map,List.getElem_range,entry,labels_count]
    by_cases h : i<d.labels.length
    · rw [ite_eq_left h,labels_lookup d i h,List.getElem_append_left h]
      rfl
    · have HE : i=d.labels.length:=by omega
      subst i
      simp only [Nat.lt_irrefl,ite_false,List.getElem_append_right (Nat.le_refl _),Nat.sub_self,List.getElem_cons_zero]

theorem good_descriptor (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) : Good n birth (labels d) a.val :=by
  refine ⟨IntegralMixedChronologicalFrameCode.labels_good d,?_,a.isLt⟩
  rwa [labels_count]

theorem point_good_descriptor (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :
    PointGood n birth (labels d) a.val g.val j.val :=by
  apply (point_good_iff n birth (labels d) a.val g.val j.val).mp
  rw [append_actual d a hk]
  refine ⟨IntegralMixedChronologicalFrameCode.labels_good _,?_,g.isLt,?_,j.isLt⟩
  · rw [labels_count]
    exact Nat.le_of_not_gt (fun h=>hg (((d.freeze a hk).frozen_mem g).mpr h))
  · rw [labels_count]
    exact Nat.le_of_not_gt (fun h=>hj (((d.freeze a hk).frozen_mem j).mpr h))

noncomputable def data (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :=
  IntegralMixedChronologicalFrameCode.data (d.freeze a hk) g j hg hj

theorem data_code (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :
    (data d a hk g j hg hj).code=code n (labels d) a.val g.val j.val :=by
  unfold code
  rw [append_actual d a hk]
  exact IntegralMixedChronologicalFrameCode.data_code (d.freeze a hk) g j hg hj

theorem data_rule (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :
    (data d a hk g j hg hj).rule=pointRule (d.freeze a hk).frame g hg j hj :=
  IntegralMixedChronologicalFrameCode.data_rule (d.freeze a hk) g j hg hj

theorem decode (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :
    IntegralMixedCausalUnitRecordBits.physical n birth (code n (labels d) a.val g.val j.val)=
      pointRule (d.freeze a hk).frame g hg j hj :=by
  unfold code
  rw [append_actual d a hk]
  exact IntegralMixedChronologicalFrameCode.decode (d.freeze a hk) g j hg hj

theorem command_currentQ {S B : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B birth ι) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n (labels d) a.val g.val j.val) hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=.critical (pointRule (d.freeze a hk).frame g hg j hj) :=by
  rw [←data_code d a hk g j hg hj]
  exact (IntegralMixedCriticalRecordConstructor.command_decode P hn _ hcap _ _).trans
    (congrArg Command.critical (data_rule d a hk g j hg hj))

theorem child_slice (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (P : SpatialSource n) (values : Fin birth→ℝ) :
    slice P (d.freeze a hk).frame values= slice P d.frame values∩{p | p ⟨d.labels.length,hk⟩=
      values ⟨birth-1-a.val,by have :=a.isLt;omega⟩} :=d.freeze_slice a hk P values

theorem actual_child_slice {S B : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B birth ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin birth→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth) (hk : d.labels.length<n+1) :
    actualSlice x φ (d.freeze a hk).frame=actualSlice x φ d.frame∩{p | p ⟨d.labels.length,hk⟩=
      values ⟨birth-1-a.val,by have :=a.isLt;omega⟩} :=by
  rw [actualSlice_eq x φ _ values H,actualSlice_eq x φ _ values H]
  exact child_slice d a hk P values

theorem code_size (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a : Fin birth)
    (hk : d.labels.length<n+1) (g j : Fin (n+1))
    (hg : g∉(d.freeze a hk).frame.frozen) (hj : j∉(d.freeze a hk).frame.frozen) :
    (code n (labels d) a.val g.val j.val).length≤IntegralMixedCriticalRecordConstructor.codeBudget n birth :=by
  rw [←data_code d a hk g j hg hj]
  exact IntegralMixedCriticalRecordConstructor.Data.code_length _

end LeanCanny.Encoding.IntegralMixedChronologicalEndpointCode
