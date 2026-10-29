/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerMass
public import LeanCanny.Encoding.FlatAffinePowerPositive

/-! # Original native mass budgets also bound the complete power system -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerPositive
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity mass)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

lemma massBound_le (F : Inputs) (u : List Bool) :
    FlatAffineCriticalStage.massBound (BoundedFullCriticalSamples.polynomial F.source u) (2 ^ (F.width u + 1))
      (max (2 ^ (F.width u + 1)) (2 * arity F u * 2 ^ (F.width u + 1))) ≤ 2 ^ mass F u := by
  let p := BoundedFullCriticalSamples.polynomial F.source u
  let S := BoundedCriticalProjection.sourceBits F.source u
  let D := (FlatAffineFullSourceTower.degree F u).size
  let W := F.width u + 1
  let N := (arity F u).size
  let T := S + D + W + N + 2
  have hpow (a b : ℕ) (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h
  have hp : MvMass.mass p ≤ 2 ^ T := (BoundedCriticalProjection.source_mass F.source u).trans (hpow S T (by omega))
  have hd : p.totalDegree * MvMass.mass p ≤ 2 ^ T := by
    have hdegree : p.totalDegree ≤ 2 ^ D := (BoundedFullCriticalSamples.source_degree F.source u).trans
      ((Nat.le_succ _).trans (Nat.lt_size_self (FlatAffineFullSourceTower.degree F u)).le)
    exact ((Nat.mul_le_mul hdegree (BoundedCriticalProjection.source_mass F.source u)).trans_eq
      (pow_add 2 D S).symm).trans (hpow (D + S) T (by omega))
  have hn : arity F u + 1 ≤ 2 ^ (N + 1) := by
    have h := Nat.lt_size_self (arity F u)
    dsimp only [N]
    rw [pow_succ]
    omega
  have hnu : (arity F u + 1) * 2 ^ W ≤ 2 ^ T := by
    exact ((Nat.mul_le_mul_right (2 ^ W) hn).trans_eq (pow_add 2 (N + 1) W).symm).trans
      (hpow (N + 1 + W) T (by omega))
  apply (FlatAffinePowerTower.massBound_le_four p (2 ^ W) (2 ^ T) (Nat.one_le_two_pow) hp hd hnu).trans_eq
  change 4 * 2 ^ T = 2 ^ (T + 2)
  rw [pow_add]
  ring

lemma raw_polynomial_mass (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourceTower.count F u)) :
    MvMass.mass (rawSystem F u i) ≤ 2 ^ mass F u :=
  (FlatAffinePowerTower.mass_le _ _ _ _ _ (2 ^ (F.width u + 1)) (2 ^ (F.width u + 1))
    (fun t => FlatAffineFullSourceTower.direction_bound F u t.val)
    (fun t => FlatAffineFullSourceTower.level_bound F u t.val) i).trans (massBound_le F u)

theorem polynomial_mass (F : Inputs) (u : List Bool) (i : Fin (FlatAffineFullSourcePositive.count F u)) :
    MvMass.mass (system F u i) ≤ 2 ^ mass F u :=
  PositivePolynomialSystem.mass_le _ _ (Nat.two_pow_pos _) (raw_polynomial_mass F u) i

end LeanCanny.Encoding.FlatAffinePowerPositive
