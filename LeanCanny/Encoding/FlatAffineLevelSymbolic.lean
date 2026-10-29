/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLevelBridge

/-! # Original ancestral level polynomials in the global input layout -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelProgram
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open scoped Classical

def embedding (F : Inputs) (ancestor : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (j : FlatAffineCriticalTower.Ancestors (FlatAffineFullSourceTower.arity F u) k) : ℕ :=
  ancestor u + (TriangularPolynomialIndexing.enumerate (FlatAffineCriticalTower.width (FlatAffineFullSourceTower.arity F u)) k j).val

theorem embedding_oldAmbient (F : Inputs) (ancestor : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (j : Fin k) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    embedding F ancestor u k (FlatAffineCriticalTower.oldAmbient k j i) =
      ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val := by
  rw [embedding, FlatAffineCriticalTower.oldAmbient_index]
  simp only [FlatAffineFullSourceTower.stageWidth, Nat.add_assoc]

theorem polynomial_eq_level (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (r : Fin (FlatAffineFullSourceTower.arity F u)) (wire : ℕ → MvPolynomial ℕ ℤ)
    (hw : ∀ j : Fin k, ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      wire (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        X (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val)) :
    AffineLevel.polynomial (inputs F base ancestor u k r.val) wire =
      rename (embedding F ancestor u k) (FlatAffineFullSourceTower.level F u k r).polynomial := by
  apply Differential.eq_of_eval_complex
  intro x
  rw [AffineLevel.polynomial_eval, eval₂_rename]
  apply value_eq_level
  intro j i
  rw [hw j i, eval₂_X, Function.comp_apply, embedding_oldAmbient]

/-- The emitted level is exactly the original tower polynomial, with all
ancestral ambient inputs retained. -/
theorem symbolic_eq_level (F : Inputs) (base ancestor : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (r : Fin (FlatAffineFullSourceTower.arity F u)) (wire : ℕ → MvPolynomial ℕ ℤ)
    (hb : ancestor u + (k + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u)
    (hw : ∀ j : Fin k, ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      wire (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        X (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val)) :
    Differential.symbolicRun wire (base u) (program F base ancestor (fun _ => k) (fun _ => r.val) u)
      (AffineLevel.packedOutput (inputs F base ancestor u k r.val)) =
      rename (embedding F ancestor u k) (FlatAffineFullSourceTower.level F u k r).polynomial :=
  (AffineLevel.packed_symbolic _ (valid F base ancestor u k r.val hb) wire).trans (polynomial_eq_level F base ancestor u k r wire hw)

end LeanCanny.Encoding.FlatAffineLevelProgram
