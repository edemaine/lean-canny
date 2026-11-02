/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalRecord
/-! # Causal serialization is the literal source-framed interpreter

Original records are stored newest first. Each instruction is instantiated
only after interpreting its older records. The original header/body tables
never serialize the resulting current-bank denominator.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def serialize {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) : (rs : List (Record n B)) → rs.length≤S+1 → {cs : List (Instruction n B) // cs.length=rs.length}
  | [],_ => ⟨[],rfl⟩
  | r::rs,h =>
    let older := serialize initial rs (by simp only [List.length_cons] at h; omega)
    let x := run initial older.val (by rw [older.property]; simp only [List.length_cons] at h; omega)
    ⟨instantiate x r::older.val,by simp only [List.length_cons,older.property]⟩

noncomputable def commands {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) := (serialize initial rs h).val

theorem commands_length {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) : (commands initial rs h).length=rs.length :=
  (serialize initial rs h).property

theorem commands_cons {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (r : Record n B) (rs : List (Record n B)) (h : (r::rs).length≤S+1) :
    commands initial (r::rs) h=instantiate (run initial (commands initial rs (by simp only [List.length_cons] at h; omega))
      (by rw [commands_length]; simp only [List.length_cons] at h; omega)) r::commands initial rs (by simp only [List.length_cons] at h; omega) := rfl

theorem commands_headers {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    (commands initial rs h).map (fun c => IntegralMixedCommandHeaderBits.command c.command)=rs.map (fun r => r.template.header) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [commands_cons,List.map_cons,instantiate_header,List.map_cons,ih]

theorem commands_words {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    IntegralMixedFramedHeaderBits.words (commands initial rs h)=
      WordList.encode (rs.reverse.map (fun r => IntegralMixedCommandHeaderBits.encode r.template.header)) := by
  have H := congrArg (fun hs : List IntegralMixedCommandHeaderBits.Header =>
    WordList.encode ((hs.map IntegralMixedCommandHeaderBits.encode).reverse)) (commands_headers initial rs h)
  simpa only [IntegralMixedFramedHeaderBits.words,List.map_map,List.map_reverse,Function.comp_def] using H

theorem commands_sources {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    (commands initial rs h).map Instruction.source=rs.map Record.source := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [commands_cons,List.map_cons,List.map_cons,ih]
    rfl

open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

theorem records_bound (P : Parameters) (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (root : List Bool) : (R root).length≤(P.cap root+1)+1 := by
  have H := hroom root
  omega

noncomputable def plan (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) : Plan P := { base with
  rules := fun root => commands (IntegralMixedFramedHistoryFamilyBits.initial P base root) (R root) (records_bound P R hroom root)
  room := fun root => by rw [commands_length]; exact hroom root }

theorem plan_initial (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (root : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.initial P (plan P base R hroom) root=
      IntegralMixedFramedHistoryFamilyBits.initial P base root := rfl

theorem plan_words (P : Parameters) (base : Plan P)
    (R : ∀ root,List (Record (P.ambient root) (P.width root)))
    (hroom : ∀ root,(R root).length+2≤P.cap root+1) (root : List Bool) :
    IntegralMixedFramedHeaderBits.words ((plan P base R hroom).rules root)=
      WordList.encode ((R root).reverse.map (fun r => IntegralMixedCommandHeaderBits.encode r.template.header)) :=
  commands_words _ _ _
end LeanCanny.Algebra.IntegralMixedCausalPlanBits
