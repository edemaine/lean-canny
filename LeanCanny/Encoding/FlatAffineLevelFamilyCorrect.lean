/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineLevelFamily

/-! # Complete shared level families in the original tower layout -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelFamily
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Algebra MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open scoped Classical

private theorem ancestor_lt (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool)
    (hb : ancestor u + (stage u + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u)
    (j : Fin (stage u)) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val < base u := by
  have hj := j.isLt
  have hi : i.val < FlatAffineFullSourceTower.stageWidth F u :=
    i.isLt.trans_le (by unfold FlatAffineFullSourceTower.stageWidth FlatAffineCriticalTower.width; omega)
  have H := Nat.mul_le_mul_right (FlatAffineFullSourceTower.stageWidth F u) (show j.val + 1 ≤ stage u + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at H
  omega

theorem output_lt (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool)
    (r : Fin (FlatAffineFullSourceTower.arity F u)) : output F base u r.val < base u + (program F base ancestor stage u).length := by
  rw [program_length]
  have H := Nat.mul_le_mul_right (stride F u) (show r.val + 1 ≤ FlatAffineFullSourceTower.arity F u from r.isLt)
  rw [Nat.add_mul, Nat.one_mul] at H
  unfold output slotBase stride at *
  omega

theorem value_sound (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool) (env : ℕ → ℂ)
    (hg : ∀ g ∈ StraightLine.gates (base u) (program F base ancestor stage u), g.Holds env)
    (z : FlatAffineCriticalTower.Ancestors (FlatAffineFullSourceTower.arity F u) (stage u) → ℂ)
    (hp : ∀ j : Fin (stage u), ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      env (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        z (FlatAffineCriticalTower.oldAmbient (stage u) j i))
    (r : Fin (FlatAffineFullSourceTower.arity F u)) :
    env (output F base u r.val) = (FlatAffineFullSourceTower.level F u (stage u) r).polynomial.eval₂ (Int.castRingHom ℂ) z := by
  rw [output_eq_slot F base ancestor u (stage u) r.val]
  apply FlatAffineLevelProgram.output_eq_level F (slotBase F base r.val) ancestor u (stage u) r env ?_ z hp
  intro g hm
  apply hg g
  change g ∈ prefixGates F base ancestor stage u (FlatAffineFullSourceTower.arity F u)
  rw [gates_range]
  exact List.mem_flatMap.mpr ⟨r.val, List.mem_range.mpr r.isLt, hm⟩

theorem exists_completion (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool)
    (hb : ancestor u + (stage u + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u) (x : ℕ → ℂ)
    (z : FlatAffineCriticalTower.Ancestors (FlatAffineFullSourceTower.arity F u) (stage u) → ℂ)
    (hp : ∀ j : Fin (stage u), ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      x (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        z (FlatAffineCriticalTower.oldAmbient (stage u) j i)) :
    ∃ env : ℕ → ℂ, (∀ i < base u, env i = x i) ∧
      (∀ g ∈ StraightLine.gates (base u) (program F base ancestor stage u), g.Holds env) ∧
      ∀ r : Fin (FlatAffineFullSourceTower.arity F u), env (output F base u r.val) =
        (FlatAffineFullSourceTower.level F u (stage u) r).polynomial.eval₂ (Int.castRingHom ℂ) z := by
  obtain ⟨env, henv, hg⟩ := StraightLine.exists_completion x (base u) (program F base ancestor stage u) (wellFormed F base ancestor stage u hb)
  refine ⟨env, henv, hg, fun r => value_sound F base ancestor stage u env hg z ?_ r⟩
  intro j i
  rw [henv _ (ancestor_lt F base ancestor stage u hb j i)]
  exact hp j i

theorem symbolic (F : Inputs) (base ancestor stage : List Bool → ℕ) (u : List Bool)
    (hb : ancestor u + (stage u + 1) * FlatAffineFullSourceTower.stageWidth F u ≤ base u)
    (wire : ℕ → MvPolynomial ℕ ℤ)
    (hw : ∀ j : Fin (stage u), ∀ i : Fin (FlatAffineFullSourceTower.arity F u),
      wire (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val) =
        X (ancestor u + j.val * FlatAffineFullSourceTower.stageWidth F u + i.val))
    (r : Fin (FlatAffineFullSourceTower.arity F u)) :
    Differential.symbolicRun wire (base u) (program F base ancestor stage u) (output F base u r.val) =
      rename (FlatAffineLevelProgram.embedding F ancestor u (stage u)) (FlatAffineFullSourceTower.level F u (stage u) r).polynomial := by
  apply Differential.eq_of_eval_complex
  intro x
  let W := Differential.symbolicRun wire (base u) (program F base ancestor stage u)
  let env : ℕ → ℂ := fun i => (W i).eval₂ (Int.castRingHom ℂ) x
  have hR : Differential.Realizes W (base u) (program F base ancestor stage u) :=
    Differential.symbolicRun_realizes wire (base u) (program F base ancestor stage u) (wellFormed F base ancestor stage u hb)
  have hg : ∀ g ∈ StraightLine.gates (base u) (program F base ancestor stage u), g.Holds env :=
    Differential.realizes_gates_eval W (base u) (program F base ancestor stage u) hR x
  rw [eval₂_rename]
  apply value_sound F base ancestor stage u env hg
  intro j i
  dsimp only [env, W]
  rw [Differential.symbolicRun_preserves_before wire (base u) (program F base ancestor stage u) _ (ancestor_lt F base ancestor stage u hb j i),
    hw j i, eval₂_X, Function.comp_apply, FlatAffineLevelProgram.embedding_oldAmbient]

end LeanCanny.Encoding.FlatAffineLevelFamily
