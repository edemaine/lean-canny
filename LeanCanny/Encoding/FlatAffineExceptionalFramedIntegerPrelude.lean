/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerCommands
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # The actual initial integer bank before changing-source instructions

Only integer commands are lifted into the initial source. Later instructions
retain their own sources. No historical critical/cut command is reinterpreted.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerPrelude
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction)
open IntegralMixedFramedHistoryFamilyBits (Plan)
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open scoped Classical

noncomputable def command {n : ℕ} (Q : SpatialSource n) (B : ℕ)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u≤B) (i : Fin (births F u)) : Instruction n B :=
  ⟨Q,hcap,FlatAffineExceptionalIntegerCommands.command Q B F C h u hB i⟩

noncomputable def commands {n : ℕ} (Q : SpatialSource n) (B : ℕ)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u≤B) : List (Instruction n B) :=
  List.ofFn (command Q B hcap F C h u hB)

theorem length_commands {n : ℕ} (Q : SpatialSource n) (B : ℕ)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u≤B) : (commands Q B hcap F C h u hB).length=births F u := List.length_ofFn

theorem chronological_commands {n : ℕ} (Q : SpatialSource n) (B : ℕ)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u≤B) (b : ℕ) (hb : b<births F u) :
    IntegralMixedFramedHistoryScript.chronological (commands Q B hcap F C h u hB) b=
      some (command Q B hcap F C h u hB (FlatAffineExceptionalIntegerCommands.index F u b hb)) := by
  unfold IntegralMixedFramedHistoryScript.chronological
  rw [List.getElem?_reverse' (j := births F u-1-b) (by rw [length_commands]; omega)]
  unfold commands
  rw [List.getElem?_ofFn]
  simp only [FlatAffineExceptionalIntegerCommands.index]
  split_ifs with hi
  · rfl
  · omega

theorem chronological_append {n : ℕ} (Q : SpatialSource n) (B : ℕ)
    (hcap : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u≤B) (later : List (Instruction n B)) (b : ℕ) (hb : b<births F u) :
    IntegralMixedFramedHistoryScript.chronological (later++commands Q B hcap F C h u hB) b=
      some (command Q B hcap F C h u hB (FlatAffineExceptionalIntegerCommands.index F u b hb)) := by
  unfold IntegralMixedFramedHistoryScript.chronological
  rw [List.reverse_append,List.getElem?_append_left (by rw [List.length_reverse,length_commands]; exact hb)]
  exact chronological_commands Q B hcap F C h u hB b hb

noncomputable def plan (P : Parameters) (base : Plan P) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (input : List Bool → List Bool)
    (later : (root : List Bool) → List (Instruction (P.ambient root) (P.width root)))
    (hW : ∀ root, width F (input root)≤P.width root)
    (hroom : ∀ root, (later root).length+births F (input root)+2≤P.cap root+1) : Plan P :=
  { base with
    rules root := later root++commands (base.initialSource root) (P.width root)
      (IntegralMixedFramedHistoryFamilyBits.initial P base root).critical_cap F C h (input root) (hW root)
    room root := by rw [List.length_append,length_commands]; exact hroom root }

end LeanCanny.Encoding.FlatAffineExceptionalFramedIntegerPrelude
