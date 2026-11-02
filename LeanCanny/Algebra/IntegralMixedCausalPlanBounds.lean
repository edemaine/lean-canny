/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlan
/-! # Causal record bounds derive actual interpreted script heights

Only original sources, integer inputs, affine rows and scales are bounded.
The omitted current-Q slope is bounded from the recursively derived old bank.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Template.core {n B : ℕ} {P : SpatialSource n} (C L : ℕ) : Template P B → Prop
  | .integer p _ _ => ∀ k,(p.coeff k).natAbs≤2^C
  | .critical r => (∀ i,(r.heights i).nodes≤L) ∧ (∀ i,(r.heights i).CoefficientsBound C) ∧
      (∀ i,(r.scales i).natAbs.size≤C)
  | .cut r => (∀ i,(r.critical.heights i).nodes≤L) ∧ (∀ i,(r.critical.heights i).CoefficientsBound C) ∧
      (∀ i,(r.critical.scales i).natAbs.size≤C)

structure OriginalBounds {n B : ℕ} (G F W D L : ℕ) (r : Record n B) : Prop where
  low : ∀ e,(r.source.low.coeff e).natAbs≤2^(F*G+1)
  leading : r.source.leading.natAbs.size≤F*G+1
  width : r.source.degree.size≤W
  degree : r.source.degree≤D
  auxiliary : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) r.source.degree≤2^B
  command : Template.core (F*G+1) L r.template

theorem instantiate_original {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) (G F W D L : ℕ) (h : OriginalBounds G F W D L r) :
    IntegralMixedFramedCurrentQGrowth.OriginalInstruction G F W D L (instantiate x r) := by
  refine ⟨h.low,h.leading,h.width,h.degree,h.auxiliary,?_⟩
  have H := h.command
  cases ht : r.template <;> simpa only [ht,Template.core,instantiate,Template.command,
    IntegralMixedFramedCurrentQGrowth.CommandCore,Cut.rule] using H

theorem instantiate_policy {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) (G F : ℕ) :
    IntegralMixedFramedCurrentQGrowth.SlopePolicy x G F (instantiate x r) := by
  cases ht : r.template with
  | integer => simp only [IntegralMixedFramedCurrentQGrowth.SlopePolicy,instantiate,Template.command,ht]
  | critical => simp only [IntegralMixedFramedCurrentQGrowth.SlopePolicy,instantiate,Template.command,ht]
  | cut c =>
    simp only [IntegralMixedFramedCurrentQGrowth.SlopePolicy,instantiate,Template.command,ht]
    by_cases hc : c.current=true
    · exact Or.inl (by simp only [Cut.rule,hc,ite_true])
    · right
      simp only [Cut.rule,hc,Bool.false_eq_true,ite_false,Int.natAbs_one]
      change 1≤F*G+1
      omega

def OriginalScript {n B : ℕ} (S W D L F C : ℕ) : List (Record n B) → Prop
  | [] => True
  | r::rs => OriginalScript S W D L F C rs ∧ OriginalBounds (height n S B W D L F C rs.length) F W D L r

theorem commands_causal {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) (W D L F C : ℕ)
    (ho : OriginalScript S W D L F C rs) :
    IntegralMixedFramedCurrentQGrowth.CausalBounds initial W D L F C (commands initial rs h)
      (by rw [commands_length]; exact h) := by
  induction rs with
  | nil => trivial
  | cons r rs ih =>
    simp only [commands_cons,IntegralMixedFramedCurrentQGrowth.CausalBounds]
    refine ⟨ih _ ho.1,?_,?_⟩
    · have ht : rs.length≤S+1 := by simp only [List.length_cons] at h; omega
      have HE : height n S B W D L F C (commands initial rs ht).length=height n S B W D L F C rs.length := by rw [commands_length]
      rw [HE]
      exact instantiate_original _ r _ _ _ _ _ ho.2
    · exact instantiate_policy _ r _ _

open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

theorem familyInputs (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (L F C : List Bool → ℕ)
    (hF : ∀ root,P.cap root+1≤F root)
    (ho : ∀ root,OriginalScript (P.cap root+1) (P.sourceWidth root) (P.degree root) (L root) (F root) (C root) (R root))
    (hd : ∀ root,InstructionBounds (C root+1) (F root) (P.sourceWidth root) (P.degree root) (L root)
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (plan P base R hroom) root)) :
    FamilyInputs P (plan P base R hroom) L F C := by
  apply IntegralMixedFramedCurrentQGrowth.family_inputs P (plan P base R hroom) L F C hF
  · intro root
    exact commands_causal (IntegralMixedFramedHistoryFamilyBits.initial P base root) (R root) _ _ _ _ _ _ (ho root)
  · exact hd
end LeanCanny.Algebra.IntegralMixedCausalPlanBits
