/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DiagonalUnivariateSystem
public import LeanCanny.Algebra.SquarefreeUniformBounds
public import LeanCanny.Encoding.SquareSampleCoordinates
public import LeanCanny.Encoding.SquareSampleComplete

/-! # A regular coordinate grid with the original primitive parameter

Replace each system equation by the square-free part of its coordinate
annihilator. The annihilator data stays unchanged, so primitive parameters
and rational coordinates agree exactly with the original input.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleGrid
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable def rowPolynomial (F : Inputs) (u : List Bool) (i : Fin (F.count u)) : Polynomial ℤ :=
  ScaledSquarefree.polynomial (F.annihilator u i)

noncomputable def budget (F : Inputs) (u : List Bool) : ℕ := F.annDegree u + F.annHeight u + 4
noncomputable def mass (F : Inputs) (u : List Bool) : ℕ := budget F u ^ 16

theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  (((h.annDegree.add h.annHeight).add (BinaryFn.const 4))).powUnary (UnaryFn.const 16)

lemma row_mass (F : Inputs) (u : List Bool) (i : Fin (F.count u)) :
    coefficientMass (rowPolynomial F u i) ≤ 2 ^ mass F u := by
  let S : SeparableBits.Family := {
    polynomial _ := F.annihilator u i
    height _ := F.annHeight u
    coefficient_bound _ j := (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) (F.ann_height u i j)) }
  exact SeparableBits.squarefree_mass_uniform S [] (budget F u) (by unfold budget; omega)
    ((F.ann_degree u i).trans (by unfold budget; omega)) (by change F.annHeight u ≤ budget F u; unfold budget; omega) (F.ann_nonzero u i)

noncomputable def system (F : Inputs) (u : List Bool) : Fin (F.count u) → MvPolynomial (Fin (F.count u)) ℤ :=
  DiagonalUnivariateSystem.system (rowPolynomial F u)

lemma roots_iff (F : Inputs) (u : List Bool) (z : Fin (F.count u) → ℝ) :
    (∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) z = 0) ↔
      ∀ i, (F.annihilator u i).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  simp only [system, DiagonalUnivariateSystem.system, DiagonalUnivariateSystem.eval,
    rowPolynomial, ScaledSquarefree.roots_iff _ (F.ann_nonzero u _)]

lemma regular (F : Inputs) (u : List Bool) (z : Fin (F.count u) → ℝ)
    (hz : ∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) z = 0) :
    (fderiv ℝ (fun x => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) x) z).IsInvertible :=
  DiagonalUnivariateSystem.regular (rowPolynomial F u)
    (fun i => ScaledSquarefree.separable_in_field _ (F.ann_nonzero u i)) z hz

noncomputable def input (F : Inputs) : Inputs where
  count := F.count
  degree u := F.annDegree u + 1
  mass := mass F
  system := system F
  count_pos := F.count_pos
  degree_pos _ := Nat.zero_lt_succ _
  system_degree u i := (DiagonalUnivariateSystem.degree_le _ _).trans
    ((ScaledSquarefree.polynomial_natDegree_le _ (F.ann_nonzero u i)).trans ((F.ann_degree u i).trans (Nat.le_succ _)))
  system_mass u i := (DiagonalUnivariateSystem.mass_le _ _).trans (row_mass F u i)
  annihilator := F.annihilator
  annDegree := F.annDegree
  annHeight := F.annHeight
  ann_nonzero := F.ann_nonzero
  ann_degree := F.ann_degree
  ann_height := F.ann_height
  ann_root u z hz _ i := (roots_iff F u z).mp hz i

theorem complete (F : Inputs) : SquareSampleComplete.Complete (input F) :=
  fun u z hz => (roots_iff F u z).mp hz

lemma parameter_eq (F : Inputs) : SquareSampleCoordinates.parameter (input F) = SquareSampleCoordinates.parameter F := rfl
lemma coordinate_eq (F : Inputs) : SquareSampleCoordinates.coordinate (input F) = SquareSampleCoordinates.coordinate F := rfl

end LeanCanny.Encoding.SquareSampleGrid
