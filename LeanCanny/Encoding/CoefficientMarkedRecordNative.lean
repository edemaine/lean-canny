/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordPrefix
/-! # Native execution of the original marked record shapes

Every birth uses the actual source and causal code constructor. Scalar birth
numbers are explicit list lengths; no complete sample or word is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordNative
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedCausalRecordBits
open scoped Classical
universe u
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def source (ctx:List Bool) (radius:List Bool→ℕ):=
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t radius ctx

theorem source_degree (ctx:List Bool) (radius:List Bool→ℕ):
    (CoefficientMarkedRecordPrefix.source (n:=n) (t:=t) ctx 0).degree=(source (n:=n) (t:=t) ctx radius).degree:=by
  unfold source CoefficientMarkedRecordPrefix.source
  rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree,
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]

theorem source_fields (ctx:List Bool) (radius:List Bool→ℕ):
    (CoefficientMarkedRecordPrefix.low (n:=n) (t:=t) ctx).map (Polynomial.evalRingHom ((2:ℤ)^radius ctx))=
      (source (n:=n) (t:=t) ctx radius).low ∧
    (CoefficientMarkedRecordPrefix.leading (n:=n) (t:=t) ctx).eval ((2:ℤ)^radius ctx)=
      (source (n:=n) (t:=t) ctx radius).leading:=by
  exact BoundedRegularRadiusLowModel.source_fields (IntegralMixedAuxiliaryMarkedIntegerSource.number n)
    (t∘IntegralMixedAuxiliaryMarkedIntegerSource.original) radius ctx

theorem source_cap (ctx:List Bool) (radius:List Bool→ℕ):
    IntegralMixedExceptionalBounds.auxiliaryCap
      (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3+1) (source (n:=n) (t:=t) ctx radius).degree≤
      2^CoefficientMarkedIntegerBirth.width hn ht ha ctx:=by
  rw [←source_degree]
  exact CoefficientMarkedRecordPrefix.source_cap hn ht ha ctx

noncomputable def cut (ctx:List Bool) (radius:List Bool→ℕ) (birth:ℕ) (code:List Bool):
    Cut (source (n:=n) (t:=t) ctx radius) (CoefficientMarkedIntegerBirth.width hn ht ha ctx):=
  IntegralMixedCausalUnitRecordBits.cut _
    (by change 0<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3;omega)
    birth code (source_cap hn ht ha ctx radius)

noncomputable instance recordIndexFintype (ambient:ℕ) (base:Type) [Fintype base]:
    (cs:List (List Bool))→Fintype (CoefficientMarkedRecordPrefix.Index ambient base cs)
  | []=>inferInstanceAs (Fintype base)
  | code::cs=>by
    letI:=recordIndexFintype ambient base cs
    change Fintype (if IntegralMixedUnitRecordCode.critical code then
      (CoefficientMarkedRecordPrefix.Index ambient base cs⊕FlatAffineCriticalStage.Variables (ambient+1))⊕Unit
      else CoefficientMarkedRecordPrefix.Index ambient base cs⊕Unit)
    split <;> infer_instance

noncomputable def instruction {S m:ℕ} {ι:Type} (ctx:List Bool) (radius:List Bool→ℕ)
    (x:State (source (n:=n) (t:=t) ctx radius) S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (code:List Bool):=
  IntegralMixedCausalRecordBits.instantiate x
    (IntegralMixedCausalUnitRecordBits.record (source (n:=n) (t:=t) ctx radius)
      (by change 0<IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3;omega)
      m code (source_cap hn ht ha ctx radius))

private theorem nativeCast_heq {α β:Sort u} (h:α=β) (v:α):HEq (cast h v) v:=by
  cases h
  rfl

private theorem step_heq {a S B m:ℕ} {P:SpatialSource a} {ι:Type} [Fintype ι]
    (x:State P S B m ι) (hm:m≤S) {c d:IntegralMixedFullHistoryScript.Command P B} (h:c=d):
    HEq (IntegralMixedFullHistoryScript.step x hm c) (IntegralMixedFullHistoryScript.step x hm d):=by
  cases h
  rfl

noncomputable def next {S m:ℕ} {ι:Type} [Fintype ι] (ctx:List Bool) (radius:List Bool→ℕ)
    (x:State (source (n:=n) (t:=t) ctx radius) S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (hm:m≤S) (code:List Bool):
    State (source (n:=n) (t:=t) ctx radius) S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) (m+1)
      (if IntegralMixedUnitRecordCode.critical code then
        (ι⊕FlatAffineCriticalStage.Variables (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3+1))⊕Unit
        else ι⊕Unit):=
  if hc:IntegralMixedUnitRecordCode.critical code=true then
    cast (congrArg (fun I:Type=>State (source (n:=n) (t:=t) ctx radius) S
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx) (m+1) I) (ite_eq_left hc).symm)
      (criticalStep x hm (IntegralMixedCausalUnitRecordBits.physical
        (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3) m code))
  else
    cast (congrArg (fun I:Type=>State (source (n:=n) (t:=t) ctx radius) S
      (CoefficientMarkedIntegerBirth.width hn ht ha ctx) (m+1) I) (ite_eq_right hc).symm)
      (IntegralMixedFullHistoryScript.step x hm
        ((Template.cut (cut hn ht ha ctx radius m code)).command (commonDenominator x) (commonDenominator_ne_zero x)))

/-- No externally supplied command is used at a native record birth. -/
theorem next_command {S m:ℕ} {ι:Type} [Fintype ι] (ctx:List Bool) (radius:List Bool→ℕ)
    (x:State (source (n:=n) (t:=t) ctx radius) S (CoefficientMarkedIntegerBirth.width hn ht ha ctx) m ι)
    (hm:m≤S) (code:List Bool):
    HEq (next hn ht ha ctx radius x hm code)
      (IntegralMixedFullHistoryScript.step x hm (instruction hn ht ha ctx radius x code).command):=by
  by_cases hc:IntegralMixedUnitRecordCode.critical code=true
  · have HC:(instruction hn ht ha ctx radius x code).command=
        .critical (IntegralMixedCausalUnitRecordBits.physical
          (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3) m code):=by
      simp only [instruction,IntegralMixedCausalRecordBits.instantiate,IntegralMixedCausalUnitRecordBits.record,
        hc,ite_true,Template.command]
      rfl
    have HL:HEq (next hn ht ha ctx radius x hm code)
        (criticalStep x hm (IntegralMixedCausalUnitRecordBits.physical
          (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3) m code)):=by
      rw [next,dite_eq_left hc]
      exact nativeCast_heq _ _
    exact HL.trans (step_heq x hm HC).symm
  · have HC:(instruction hn ht ha ctx radius x code).command=
        (Template.cut (cut hn ht ha ctx radius m code)).command (commonDenominator x) (commonDenominator_ne_zero x):=by
      simp only [instruction,IntegralMixedCausalRecordBits.instantiate,IntegralMixedCausalUnitRecordBits.record,
        hc]
      rfl
    have HL:HEq (next hn ht ha ctx radius x hm code)
        (IntegralMixedFullHistoryScript.step x hm
          ((Template.cut (cut hn ht ha ctx radius m code)).command (commonDenominator x) (commonDenominator_ne_zero x))):=by
      rw [next,dite_eq_right hc]
      exact nativeCast_heq _ _
    exact HL.trans (step_heq x hm HC).symm

noncomputable def run (ctx:List Bool) (radius:List Bool→ℕ) (S:ℕ):
    (cs:List (List Bool))→(CoefficientMarkedPreludeActual.indices n ctx).length+cs.length≤S+1→
    State (source (n:=n) (t:=t) ctx radius) S (CoefficientMarkedIntegerBirth.width hn ht ha ctx)
      ((CoefficientMarkedPreludeActual.indices n ctx).length+cs.length)
      (CoefficientMarkedRecordPrefix.Index (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+3)
        (CoefficientMarkedPreludePrefix.Index (CoefficientMarkedPreludeActual.indices n ctx)) cs)
  | [],h=>CoefficientMarkedPreludePrefix.nativeRun hn ht ha ctx radius S (CoefficientMarkedPreludeActual.indices n ctx)
      (by simpa only [List.length_nil,Nat.add_zero] using h)
  | code::cs,h=>
    next hn ht ha ctx radius
      (run ctx radius S cs (by simp only [List.length_cons] at h;omega))
      (by simp only [List.length_cons] at h;omega) code

end LeanCanny.Encoding.CoefficientMarkedRecordNative
