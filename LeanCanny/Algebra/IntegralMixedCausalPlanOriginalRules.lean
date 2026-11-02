/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanSnapshot
/-! # Source-independent original rules survive causal instantiation

Only affine/scales observations are transported. This statement makes no
claim that the physical states of a scalar shadow and native plan coincide.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def originalPhysical {n B : ℕ} (r : Record n B) : CriticalRule n :=
  match r.template with | .critical c => c | _ => IntegralMixedFullPhysicalBits.defaultRule n
noncomputable def originalVirtual {n B : ℕ} (r : Record n B) (fallback : CriticalRule n) : CriticalRule n :=
  match r.template with | .cut c => c.critical | _ => fallback
noncomputable def instructionPhysical {n B : ℕ} (c : Instruction n B) : CriticalRule n :=
  match c.command with | .critical r => r | _ => IntegralMixedFullPhysicalBits.defaultRule n
noncomputable def instructionVirtual {n B : ℕ} (c : Instruction n B) (fallback : CriticalRule n) : CriticalRule n :=
  match c.command with | .cut r _ _ _ _ => r.critical | _ => fallback

theorem instantiate_physical {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) : instructionPhysical (instantiate x r)=originalPhysical r := by
  cases ht : r.template <;> simp only [instructionPhysical,instantiate,Template.command,ht,originalPhysical]

theorem instantiate_virtual {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (r : Record n B) (fallback : CriticalRule n) :
    instructionVirtual (instantiate x r) fallback=originalVirtual r fallback := by
  cases ht : r.template <;> simp only [instructionVirtual,instantiate,Template.command,ht,originalVirtual,Cut.rule]

theorem commands_physical {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    (commands initial rs h).map instructionPhysical=rs.map originalPhysical := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [commands_cons,List.map_cons,instantiate_physical,List.map_cons,ih]

theorem commands_virtual {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) (fallback : CriticalRule n) :
    (commands initial rs h).map (fun c => instructionVirtual c fallback)=rs.map (fun r => originalVirtual r fallback) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [commands_cons,List.map_cons,instantiate_virtual,List.map_cons,ih]

private theorem option_map_getD {α β : Type} (f : α→β) (o : Option α) (d : α) : f (o.getD d)=(o.map f).getD (f d) := by
  cases o <;> rfl

theorem physical_rule_original (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (key : List Bool) :
    IntegralMixedFramedPhysicalBits.rule P (plan P base R hroom) key=
      ((R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?.map originalPhysical).getD
        (IntegralMixedFullPhysicalBits.defaultRule _) := by
  let initial := IntegralMixedFramedHistoryFamilyBits.initial P base (pairFst key)
  let rs := R (pairFst key)
  let b := IntegralMixedFramedHistoryFamilyBits.prefixLength P key
  have H := congrArg (fun cs => cs.reverse[b]?) (commands_physical initial rs (records_bound P R hroom _))
  rw [← List.map_reverse,← List.map_reverse,List.getElem?_map,List.getElem?_map] at H
  have HE : IntegralMixedFramedPhysicalBits.rule P (plan P base R hroom) key=
      instructionPhysical (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key) := by
    unfold IntegralMixedFramedPhysicalBits.rule instructionPhysical
    cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key).command <;> rfl
  rw [HE]
  let fallbackI := IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (plan P base R hroom) (pairFst key)
  change instructionPhysical ((chronological (commands initial rs (records_bound P R hroom _)) b).getD fallbackI)=_
  rw [option_map_getD instructionPhysical]
  change (Option.map instructionPhysical (commands initial rs (records_bound P R hroom _)).reverse[b]?).getD _=_
  rw [H]
  rfl

theorem virtual_rule_original (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (hn : ∀ root,0<P.ambient root)
    (hd : ∀ root,∀ r∈R root,r.source.degree=P.degree root)
    (hW : ∀ root,(P.degree root).size≤P.sourceWidth root) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family P (plan P base R hroom) (data P base R hroom hn hd hW)).rule key).critical=
      ((R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?.map
        (fun r => originalVirtual r (fallbackRule _ (hn _)).critical)).getD (fallbackRule _ (hn _)).critical := by
  let initial := IntegralMixedFramedHistoryFamilyBits.initial P base (pairFst key)
  let rs := R (pairFst key)
  let b := IntegralMixedFramedHistoryFamilyBits.prefixLength P key
  let fallback := (fallbackRule _ (hn (pairFst key))).critical
  have H := congrArg (fun cs => cs.reverse[b]?) (commands_virtual initial rs (records_bound P R hroom _) fallback)
  rw [← List.map_reverse,← List.map_reverse,List.getElem?_map,List.getElem?_map] at H
  have HE : ((IntegralMixedFramedHistoryFamilyBits.family P (plan P base R hroom) (data P base R hroom hn hd hW)).rule key).critical=
      instructionVirtual (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key) fallback := by
    change (IntegralMixedFramedHistoryFamilyBits.selection P _ _ key).rule.critical=_
    unfold IntegralMixedFramedHistoryFamilyBits.selection instructionVirtual
    cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key).command <;> rfl
  rw [HE]
  change instructionVirtual ((chronological (commands initial rs (records_bound P R hroom _)) b).getD _) fallback=_
  rw [option_map_getD (fun c => instructionVirtual c fallback)]
  change (Option.map (fun c => instructionVirtual c fallback) (commands initial rs (records_bound P R hroom _)).reverse[b]?).getD _=_
  rw [H]
  rfl

end LeanCanny.Algebra.IntegralMixedCausalPlanBits
