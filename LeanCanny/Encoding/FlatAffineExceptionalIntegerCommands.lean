/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalBankSource
public import LeanCanny.Algebra.IntegralMixedIntegerProducerOriginalSource
/-! # Literal initial mixed commands for the actual exceptional parent bank -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerCommands
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width finitePolynomial)
open scoped Classical

noncomputable def command {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) (i : Fin (births F u)) : Command P B :=
  .integer (finitePolynomial F C h u i) (FlatAffineExceptionalBankSource.finite_nonzero F C h u i)
    ((FlatAffineExceptionalBankSource.finite_degree_cap F C h u i).trans
      (Nat.pow_le_pow_right (by decide) hB))
noncomputable def commands {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) : List (Command P B) :=
  List.ofFn (command P B F C h u hB)

theorem length_commands {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) : (commands P B F C h u hB).length = births F u := List.length_ofFn

noncomputable def index (F : Inputs) (u : List Bool) (b : ℕ) (hb : b < births F u) : Fin (births F u) :=
  ⟨births F u - 1 - b, by omega⟩

theorem chronological_commands {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) (b : ℕ) (hb : b < births F u) :
    chronological (commands P B F C h u hB) b = some (command P B F C h u hB (index F u b hb)) := by
  unfold chronological
  rw [List.getElem?_reverse' (j := births F u - 1 - b) (by rw [length_commands]; omega)]
  unfold commands
  rw [List.getElem?_ofFn]
  simp only [index]
  split_ifs with hi
  · rfl
  · omega

theorem chronological_append {n : ℕ} (P : SpatialSource n) (B : ℕ) (F : Inputs)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (u : List Bool) (hB : width F u ≤ B) (cs : List (Command P B)) (b : ℕ) (hb : b < births F u) :
    chronological (cs ++ commands P B F C h u hB) b = some (command P B F C h u hB (index F u b hb)) := by
  unfold chronological
  rw [List.reverse_append, List.getElem?_append_left (by rw [List.length_reverse, length_commands]; exact hb)]
  exact chronological_commands P B F C h u hB b hb

end LeanCanny.Encoding.FlatAffineExceptionalIntegerCommands
