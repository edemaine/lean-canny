/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerInfinity
public import LeanCanny.Encoding.SquareSampleComplete
public import LeanCanny.Encoding.SquareSampleAccess

/-! # Complete square sampling for the actual affine power tower

Cone certificates are mathematical promises on the original stage records.
All numerical controls and coefficient readers come from those same inputs;
the annihilators capture singular roots as well as regular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerSampleInput
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local irreducible] FlatAffinePowerPositive.system FlatAffinePowerPositive.degree

noncomputable def polynomial (F : Inputs) (u : List Bool) (i : Fin (count F u)) : Polynomial ℤ :=
  AffineFiniteCoordinates.annihilator (FlatAffinePowerPositive.system F u) (FlatAffinePowerPositive.degree F u) i

lemma polynomial_comp (F : Inputs) (f : List Bool → List Bool) (u : List Bool) (i : Fin (count F (f u))) :
    polynomial (FlatAffineFullSourceContext.comp F f) u i = polynomial F (f u) i :=
  congrArg₂ (fun p d => AffineFiniteCoordinates.annihilator p d i)
    (funext (FlatAffinePowerPositive.system_comp F f u)) (funext (FlatAffinePowerPositive.degree_comp F f u))

lemma polynomial_degree (F : Inputs) (u : List Bool) (i : Fin (count F u)) :
    (polynomial F u i).natDegree ≤ FlatAffinePowerGram.degreeBound F u := by
  have h := AffineFiniteCoordinates.degree_le (FlatAffinePowerPositive.system F u) (FlatAffinePowerPositive.degree F u) i
  have he : AffineFiniteCoordinates.dimension (FlatAffinePowerPositive.degree F u) = FlatAffinePowerGramLayout.dimension F u := by
    unfold AffineFiniteCoordinates.dimension FlatAffinePowerGramLayout.dimension
    rw [FlatAffinePowerGramLayout.width_eq]
  simpa only [polynomial, he, FlatAffinePowerGram.degreeBound] using h

lemma polynomial_height (F : Inputs) (u : List Bool) (i : Fin (count F u)) (j : ℕ) :
    ((polynomial F u i).coeff j).natAbs.size ≤ FlatAffinePowerGram.heightBound F u := by
  let coordinate : (v : List Bool) → Fin (count F v) := fun v =>
    ⟨min i.val (count F v - 1), by have := FlatAffineFullSourcePositive.count_pos F v; omega⟩
  have hi : coordinate u = i := Fin.ext (Nat.min_eq_left (by have := i.isLt; omega))
  have h := FlatAffinePowerGram.annihilator_height_le F coordinate u j
  rw [FlatAffinePowerGram.annihilator_eq, hi] at h
  exact h

lemma polynomial_root {K : Type*} [Field K] (F : Inputs) (u : List Bool) (z : Fin (count F u) → K)
    (hz : ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom K) z = 0) (i : Fin (count F u)) :
    (polynomial F u i).eval₂ (Int.castRingHom K) (z i) = 0 :=
  AffineFiniteCoordinates.eval_eq_zero _ _ (FlatAffinePowerPositive.polynomial_degree F u) z hz i

noncomputable def input (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) : SquareSampleInput.Inputs where
  count := count F
  degree := FlatAffineFullSourceTower.degree F
  mass := FlatAffineFullSourceTower.mass F
  system := FlatAffinePowerPositive.system F
  count_pos := FlatAffineFullSourcePositive.count_pos F
  degree_pos := FlatAffineFullSourceTower.degree_pos F
  system_degree := FlatAffinePowerPositive.uniform_polynomial_degree F
  system_mass := FlatAffinePowerPositive.polynomial_mass F
  annihilator := polynomial F
  annDegree := FlatAffinePowerGram.degreeBound F
  annHeight := FlatAffinePowerGram.heightBound F
  ann_nonzero u i := AffineFiniteCoordinates.ne_zero _ _ (FlatAffinePowerPositive.degree_pos F u)
    (FlatAffinePowerPositive.noInfinity F hcone u) i
  ann_degree := polynomial_degree F
  ann_height := polynomial_height F
  ann_root u z hz _ i := polynomial_root F u z hz i

theorem complete (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    SquareSampleComplete.Complete (input F hcone) := polynomial_root F

end LeanCanny.Encoding.FlatAffinePowerSampleInput
