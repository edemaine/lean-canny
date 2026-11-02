/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanLookup
/-! # Total source snapshots and defaults of the concrete causal plan

Source lookup uses only the original record table and scalar birth. Missing
records use the original initial source and a literal zero/unit fallback.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem option_source {n B : ℕ} (o : Option (Instruction n B)) (fallback : Instruction n B) :
    (o.getD fallback).source=(o.map Instruction.source).getD fallback.source := by cases o <;> rfl

theorem commands_source_getD {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1)
    (fallback : Instruction n B) (b : ℕ) :
    ((chronological (commands initial rs h) b).getD fallback).source=
      (rs.reverse[b]?.map Record.source).getD fallback.source := by
  rw [option_source,chronological_source]

noncomputable def selectedSource (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root))) (key : List Bool) : SpatialSource (P.ambient (pairFst key)) :=
  ((R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]?.map Record.source).getD
    (base.initialSource (pairFst key))

theorem instruction_source (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key).source=selectedSource P base R key :=
  commands_source_getD _ _ _ _ _

theorem source_degree (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hd : ∀ root,∀ r∈R root,r.source.degree=P.degree root) (key : List Bool) :
    (selectedSource P base R key).degree=P.degree (pairFst key) := by
  unfold selectedSource
  cases hr : (R (pairFst key)).reverse[IntegralMixedFramedHistoryFamilyBits.prefixLength P key]? with
  | none => exact base.initial_degree (pairFst key)
  | some r => exact hd _ r (List.mem_reverse.mp (List.mem_of_getElem? hr))

noncomputable def fallbackRule (n : ℕ) (hn : 0<n) : IntegralMixedCriticalSweep.Rule n where
  critical := {
    offset := ⟨1,by omega⟩
    objective := 0
    coordinate := 0
    scales _ := 1
    scales_ne_zero _ := one_ne_zero
    heights _ := .constant 0 }
  height := ⟨0,Nat.succ_pos _⟩
  height_frozen := by change 0<1; omega
  slope := 1
  slope_ne_zero := one_ne_zero

noncomputable def fallback {n : ℕ} (S : SpatialSource n) (hn : 0<n) : IntegralMixedFullHistoryFamilyBits.Selection S :=
  ⟨fallbackRule n hn,
    .coordinate ⟨0,Nat.succ_pos _⟩ ⟨0,Nat.succ_pos _⟩,0,Nat.zero_le _⟩

noncomputable def data (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (hn : ∀ root,0<P.ambient root)
    (hd : ∀ root,∀ r∈R root,r.source.degree=P.degree root)
    (hW : ∀ root,(P.degree root).size≤P.sourceWidth root) :
    IntegralMixedFramedHistoryFamilyBits.Data P (plan P base R hroom) where
  degree_eq key := (congrArg SpatialSource.degree (instruction_source P base R hroom key)).trans (source_degree P base R hd key)
  sourceWidth key := by rw [instruction_source,source_degree P base R hd key]; exact hW (pairFst key)
  fallback key := fallback (IntegralMixedFramedHistoryFamilyBits.instruction P (plan P base R hroom) key).source (hn (pairFst key))
end LeanCanny.Algebra.IntegralMixedCausalPlanBits
