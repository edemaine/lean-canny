/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerGram
public import LeanCanny.Encoding.FlatAffinePowerBounds

/-! # Native degree and coefficient-size budgets for complete annihilators

The full-box dimension bounds the degree. Its factorial determinant mass
bound gives a binary coefficient-size control from the original source mass.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerGram
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs mass)
open FlatAffineFullSourcePositive (count)
open FlatAffinePowerGramLayout (dimension)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatAffinePowerPositive.system FlatAffinePowerPositive.degree

noncomputable def degreeBound (F : Inputs) (c : List Bool) : ℕ := dimension F c + 1
noncomputable def heightBound (F : Inputs) (c : List Bool) : ℕ :=
  (dimension F c).size * dimension F c + dimension F c * mass F c + 1

theorem degreeBound_binary {F : Inputs} (h : F.Access) : BinaryFn (degreeBound F) :=
  (FlatAffinePowerGramLayout.dimension_binary h).add (BinaryFn.const 1)

theorem heightBound_binary {F : Inputs} (h : F.Access) : BinaryFn (heightBound F) := by
  have hn := FlatAffinePowerGramLayout.dimension_binary h
  exact ((hn.size.mul hn).add (hn.mul (FlatAffineFullSourceTower.mass_binary h))).add (BinaryFn.const 1)

lemma annihilator_height_le (F : Inputs) (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) (j : ℕ) :
    ((annihilator F coordinate c).coeff j).natAbs.size ≤ heightBound F c := by
  let N := dimension F c
  let b := mass F c
  have hb : 1 ≤ b := by dsimp [b, mass]; omega
  have hM : 2 ≤ 2 ^ b := by simpa only [pow_one] using Nat.pow_le_pow_right (n := 2) (by decide) hb
  have hsource (i : Fin (count F c)) (e : Fin (count F c) →₀ ℕ) :
      ((FlatAffinePowerPositive.system F c i).coeff e).natAbs ≤ 2 ^ b :=
    (MvMass.coeff_le _ _).trans (FlatAffinePowerPositive.polynomial_mass F c i)
  have hmass := AffineBoxGramEliminant.annihilator_mass_le
    (AffineFiniteCoordinates.homogeneousRows (FlatAffinePowerPositive.system F c) (FlatAffinePowerPositive.degree F c))
    (FlatAffinePowerPositive.degree F c) (FlatAffinePowerControls.width F c) (2 ^ b) hM
    (AffineFiniteCoordinates.homogeneous_coefficient_bound _ _ (2 ^ b) hsource) (coordinate c).succ
  have hfac : N.factorial ≤ 2 ^ (N.size * N) :=
    (Nat.factorial_le_pow N).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self N).le N).trans_eq (pow_mul _ _ _).symm)
  have hbound : ((annihilator F coordinate c).coeff j).natAbs ≤ 2 ^ (N.size * N + N * b) := by
    calc
      _ ≤ coefficientMass (annihilator F coordinate c) := coeff_natAbs_le_coefficientMass _ _
      _ ≤ N.factorial * (2 ^ b) ^ N := hmass
      _ ≤ 2 ^ (N.size * N) * (2 ^ b) ^ N := Nat.mul_le_mul_right _ hfac
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm b]
  change _ ≤ N.size * N + N * b + 1
  simpa only [Nat.size_pow] using Nat.size_le_size hbound

/-- Every field-valued system root is retained; no Jacobian condition is used. -/
lemma annihilator_eval_eq_zero {K : Type*} [Field K] (F : Inputs)
    (coordinate : (c : List Bool) → Fin (count F c)) (c : List Bool) (z : Fin (count F c) → K)
    (hz : ∀ i, (FlatAffinePowerPositive.system F c i).eval₂ (Int.castRingHom K) z = 0) :
    (annihilator F coordinate c).eval₂ (Int.castRingHom K) (z (coordinate c)) = 0 := by
  rw [annihilator_eq]
  exact AffineFiniteCoordinates.eval_eq_zero _ _ (FlatAffinePowerPositive.polynomial_degree F c) z hz (coordinate c)

end LeanCanny.Encoding.FlatAffinePowerGram
