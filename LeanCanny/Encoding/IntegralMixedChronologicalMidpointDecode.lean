/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointActual
/-! # Original midpoint records have exact guards, decode and current-Q steps -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFullHistoryScript
open LeanCanny.Geometry LeanCanny.Geometry.IntegralMixedFrozenFrame
open IntegralMixedCriticalRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}
open IntegralMixedChronologicalFrameCode (labels labels_count)

 theorem good_descriptor (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    Good n birth (labels d) a.val b.val g.val j.val :=by
  refine ⟨IntegralMixedChronologicalFrameCode.labels_good d,a.isLt,b.isLt,?_,g.isLt,?_,j.isLt⟩
  · simpa only [labels_count] using (IntegralMixedChronologicalMidpoint.free_iff d hk a b g).mp hg
  · simpa only [labels_count] using (IntegralMixedChronologicalMidpoint.free_iff d hk a b j).mp hj

theorem decode (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    IntegralMixedCausalUnitRecordBits.physical n birth (code n (labels d) a.val b.val g.val j.val)=
      pointRule (IntegralMixedChronologicalMidpoint.frame d hk a b) g hg j hj :=by
  rw [←data_code d hk a b g j hg hj]
  exact (rule_decode _).trans (data_rule d hk a b g j hg hj)

theorem command_currentQ {S B : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B birth ι) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (IntegralMixedCausalUnitRecordBits.record P hn birth (code n (labels d) a.val b.val g.val j.val) hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x)=
        .critical (pointRule (IntegralMixedChronologicalMidpoint.frame d hk a b) g hg j hj) :=by
  rw [←data_code d hk a b g j hg hj]
  exact (command_decode P hn _ hcap _ _).trans (congrArg Command.critical (data_rule d hk a b g j hg hj))

private theorem step_command_heq {S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B birth ι) (hm : birth≤S) (c e : Command P B) (hc : c=e) :
    HEq (step x hm c) (step x hm e) :=by
  cases hc
  rfl

theorem step_currentQ {S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B birth ι) (hm : birth≤S) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    HEq (step x hm ((IntegralMixedCausalUnitRecordBits.record P hn birth
      (code n (labels d) a.val b.val g.val j.val) hcap).template.command
        (commonDenominator x) (commonDenominator_ne_zero x)))
      (criticalStep x hm (pointRule (IntegralMixedChronologicalMidpoint.frame d hk a b) g hg j hj)) :=
  step_command_heq x hm _ _ (command_currentQ x hn hcap d hk a b g j hg hj)

theorem actual_slice_eq {S B : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B birth ι) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin birth→ℝ)
    (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1) (a b : Fin birth) :
    actualSlice x φ (IntegralMixedChronologicalMidpoint.frame d hk a b)=
      actualSlice x φ d.frame∩{p | p (IntegralMixedChronologicalMidpoint.next d hk)=
        (values (IntegralMixedChronologicalMidpoint.reference a)+values (IntegralMixedChronologicalMidpoint.reference b))/2} :=by
  rw [actualSlice_eq x φ _ values H,actualSlice_eq x φ _ values H]
  exact IntegralMixedChronologicalMidpoint.slice_eq d hk a b P values

theorem code_size (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (code n (labels d) a.val b.val g.val j.val).length≤IntegralMixedCriticalRecordConstructor.codeBudget n birth :=by
  rw [←data_code d hk a b g j hg hj]
  exact Data.code_length _

theorem retained_labels (d : IntegralMixedChronologicalFrame.Descriptor n birth) : labels d.retain=labels d :=by
  unfold labels IntegralMixedChronologicalFrame.Descriptor.retain
  rw [List.map_map]
  rfl

theorem code_retain (d : IntegralMixedChronologicalFrame.Descriptor n birth) (a b : Fin birth) (g j : ℕ) :
    code n (labels d.retain) a.castSucc.val b.castSucc.val g j=code n (labels d) a.val b.val g j :=by
  rw [retained_labels]
  rfl

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
