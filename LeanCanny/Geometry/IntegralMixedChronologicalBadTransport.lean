/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepNormalized
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotBad
/-! # Ordinary bad roots transfer through the actual frozen reference values -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedFrozenFrame IntegralMixedChronologicalFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem mem_bad_imp_of_reference_values (e : IntegralMixedPrefixSnapshot.Data)
    {S B m : ℕ} {ι : Type} (x : State e.source S B m ι) (hm : m≤S)
    (d : Descriptor e.ambient m) (hk : d.labels.length<e.ambient+1)
    (g : Fin (e.ambient+1)) (hg : g∉(frame d hk).frozen) (hgv : g.val=d.labels.length+1)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (V : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=V i)
    (choices : IntegralMixedRelativeCuts.Choices x hm
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) φ)
    (values : ℕ→ℝ)
    (hv : ∀i : Fin d.labels.length,values (e.birth-1-(d.labels.get i).val)=V (d.reference i))
    (a : ℝ) (ha : a∈e.bad (IntegralMixedChronologicalFrameCode.labels d) values) :
    a∈IntegralMixedSelectedCriticalCuts.bad x hm
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) φ choices := by
  let labels := IntegralMixedChronologicalFrameCode.labels d
  unfold IntegralMixedPrefixSnapshot.Data.bad at ha
  split_ifs at ha with hr
  · rcases ha with ⟨ψ,hψ,c,hc⟩
    let dd := IntegralMixedChronologicalFrameCode.descriptor e.ambient e.birth labels hr.2.1
    have HL : dd.labels.length=d.labels.length :=
      (IntegralMixedChronologicalFrameCode.descriptor_length _ _ _ _).trans
        (IntegralMixedChronologicalFrameCode.labels_count d)
    have hkk : dd.labels.length<e.ambient+1 := by rw [HL];exact hk
    let gg : Fin (e.ambient+1) := ⟨WordListRecords.count labels+1,hr.2.2⟩
    have hgg : gg∉(frame dd hkk).frozen := by rw [free_iff,HL];rw [←IntegralMixedChronologicalFrameCode.labels_count d]
    have HR : e.rule labels hr=(data dd hkk gg gg hgg hgg).rule
        (commonDenominator e.state) (commonDenominator_ne_zero e.state) := rfl
    have HLabel (i : Fin d.labels.length) : (dd.labels.get ⟨i.val,by rw [HL];exact i.isLt⟩).val=(d.labels.get i).val := by
      have HH := IntegralMixedChronologicalFrameCode.descriptor_lookup e.ambient e.birth labels hr.2.1 i.val
        (by rw [IntegralMixedChronologicalFrameCode.labels_count];exact i.isLt)
      rw [IntegralMixedChronologicalFrameCode.labels_lookup dd i.val (by rw [HL];exact i.isLt),
        IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt] at HH
      exact HH
    have HNorm : ∀i,i<((data d hk g g hg hg).rule (commonDenominator x)
        (commonDenominator_ne_zero x)).critical.offset.val→
        IntegralMixedNumericalSweep.normalized ((data d hk g g hg hg).rule (commonDenominator x)
          (commonDenominator_ne_zero x)) V i=
        IntegralMixedNumericalSweep.normalized (e.rule labels hr) (fun j : Fin e.birth=>values j.val) i := by
      intro i hi
      rw [data_rule_offset] at hi
      rw [HR,normalized_data d hk g g hg hg _ _ V i hi,
        normalized_data dd hkk gg gg hgg hgg _ _ (fun j : Fin e.birth=>values j.val) i (by omega)]
      by_cases hi' : i<d.labels.length
      · rw [dite_eq_left hi',dite_eq_left (show i<dd.labels.length by omega)]
        apply congrArg Polynomial.C
        have HE := HLabel ⟨i,hi'⟩
        change V (d.reference ⟨i,hi'⟩)=values (e.birth-1-(dd.labels.get ⟨i,_⟩).val)
        rw [HE]
        exact (hv ⟨i,hi'⟩).symm
      · rw [dite_eq_right hi',dite_eq_right (show ¬i<dd.labels.length by omega)]
    have HO : ((data d hk g g hg hg).rule (commonDenominator x)
        (commonDenominator_ne_zero x)).critical.offset=(e.rule labels hr).critical.offset := by
      apply Fin.ext
      rw [HR,data_rule_offset,data_rule_offset,HL]
    have HG : ((data d hk g g hg hg).rule (commonDenominator x)
        (commonDenominator_ne_zero x)).critical.objective=(e.rule labels hr).critical.objective := by
      rw [HR,data_rule_objective,data_rule_objective,hgv,HL]
      change d.labels.length+1-(d.labels.length+1)=WordListRecords.count labels+1-(d.labels.length+1)
      rw [IntegralMixedChronologicalFrameCode.labels_count]
    have HB := IntegralMixedNumericalSweep.bad_iff x hm e.state hr.1
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) (e.rule labels hr)
      rfl (by rw [HR];rfl) HO HG φ ψ V (fun j : Fin e.birth=>values j.val) H hψ HNorm choices c a
    exact HB.mp hc
  · exact False.elim ha

theorem mem_bad_imp_of_reference_values_heq (e : IntegralMixedPrefixSnapshot.Data)
    {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (en : n=e.ambient) (hSource : HEq P e.source) (x : State P S B m ι) (hm : m≤S)
    (d : Descriptor n m) (hk : d.labels.length<n+1)
    (g : Fin (n+1)) (hg : g∉(frame d hk).frozen) (hgv : g.val=d.labels.length+1)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (V : Fin m→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=V i)
    (choices : IntegralMixedRelativeCuts.Choices x hm
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) φ)
    (values : ℕ→ℝ)
    (hv : ∀i : Fin d.labels.length,values (e.birth-1-(d.labels.get i).val)=V (d.reference i))
    (a : ℝ) (ha : a∈e.bad (IntegralMixedChronologicalFrameCode.labels d) values) :
    a∈IntegralMixedSelectedCriticalCuts.bad x hm
      ((data d hk g g hg hg).rule (commonDenominator x) (commonDenominator_ne_zero x)) φ choices := by
  subst n
  have HP : P=e.source := eq_of_heq hSource
  subst P
  exact mem_bad_imp_of_reference_values e x hm d hk g hg hgv φ V H choices values hv a ha

end LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
