/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointEndpointRecord
public import LeanCanny.Encoding.IntegralMixedChosenCutRecordBounds
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRealCriticalRecord
/-! # Every actual slab endpoint has a bounded exact decoded full extension

Exceptional endpoints use the actual selected factor. Critical heights use
an actual real critical point. No ghost annihilator root is treated as a
physical point and no arbitrary record solvability is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralHistorySampler UniformIntegralPowerSchedule IntegralMixedChosenLocalRealization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem joint_endpoint_record_bounded (x : State P S B m ι) (hm : m≤S) (hn : 0<n)
    (charge : ℕ) (hdegree : P.degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (F : Frame n) (HF : FreeNormal F) (HA : AtomicRows F m) (HP : PrefixFrozen F)
    (h : Fin (n+1)) (hh : h∉F.frozen) (g : Fin (n+1)) (hg : g∉(line F h).frozen)
    (z : ι→ℝ) (hz : ∀ i,(x.sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=z (x.sampler.scalar i)^weights S (2^B) m i)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (old : IntegralMixedRelativeCuts.Choices x hm (cutRule x F h g hg) φ)
    (a : ℝ) (ha : a∈jointEndpointSet x hm φ F h g hg values old) :
    ∃ code : List Bool,code.length≤IntegralMixedCutRecordConstructor.codeBudget n m B ∧
      Encoded x hm hn hcap z φ values a code :=by
  rcases ha with Hbad|Hreal
  · obtain ⟨j,Hj⟩:=Hbad
    let d:=(HA.line h).sweepData h (Finset.mem_insert_self h F.frozen) g hg
    have HD : d.rule (commonDenominator x) (commonDenominator_ne_zero x)=cutRule x F h g hg:=
      (HA.line h).sweepData_rule x h (Finset.mem_insert_self h F.frozen) g hg
    let k:=LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.kind x hm (cutRule x F h g hg) φ old j
    have HK:=LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.kind_valid x hm (cutRule x F h g hg) φ old j
    let w:=CutChoice.ofRule x hm φ d (cutRule x F h g hg) HD k HK a Hj
    have HW : w.value=a:=CutChoice.ofRule_value x hm φ d _ HD k HK a Hj
    refine ⟨w.code x hm φ,w.code_length x hm φ hcap,?_⟩
    simpa only [HW] using IntegralMixedChosenLocalRealization.cut x hm hn hcap z hz φ hφ values H w
  · exact ⟨(HA.pointData h h hh hh).code,
      (HA.pointData h h hh hh).code_length.trans (IntegralMixedCutRecordConstructor.critical_codeBudget_le n m B),
      HP.realCriticalValue_record x hm hn charge hdegree hcap F HF HA h hh z hz φ hφ values H a Hreal⟩


def jointSlabByteBudget (n m B : ℕ) : ℕ:=
  (2*(IntegralMixedCutRecordConstructor.codeBudget n m B+
    IntegralMixedCutRecordConstructor.codeBudget n (m+1) B+
    IntegralMixedCutRecordConstructor.codeBudget n (m+2) B)+2)*3

theorem joint_slab_code_bytes (codeA codeB codeM : List Bool)
    (HA : codeA.length≤IntegralMixedCutRecordConstructor.codeBudget n m B)
    (HB : codeB.length≤IntegralMixedCutRecordConstructor.codeBudget n (m+1) B)
    (HM : codeM.length≤IntegralMixedCutRecordConstructor.codeBudget n (m+2) B) :
    (WordList.encode [codeA,codeB,codeM]).length≤jointSlabByteBudget n m B :=by
  let V:=IntegralMixedCutRecordConstructor.codeBudget n m B+
    IntegralMixedCutRecordConstructor.codeBudget n (m+1) B+
    IntegralMixedCutRecordConstructor.codeBudget n (m+2) B
  have HF : ∀ w∈[codeA,codeB,codeM],w.length≤V:=by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl <;> dsimp only [V] <;> omega
  simpa only [jointSlabByteBudget,List.length_cons,List.length_nil] using WordList.length_le _ V HF

end LeanCanny.Geometry.IntegralMixedFrozenFrame
