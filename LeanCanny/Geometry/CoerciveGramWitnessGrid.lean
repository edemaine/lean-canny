/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CoerciveGramComponentGrid
/-! # Bounded witnessed Gram slices give total nonzero diagonal heads -/
@[expose] public section
namespace LeanCanny.Geometry.CoerciveGramWitnessGrid
open LeanCanny.Algebra Set MvPolynomial
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CoerciveBoxGramEliminant.polynomial
variable {n : ℕ}

noncomputable def polynomial (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (tau witness : Fin n → ℕ) (i : Fin n) : Polynomial ℤ :=
  let p := (CoerciveBoxGramEliminant.polynomial q D i).coeff (tau i)
  if p.coeff (witness i) = 0 then 1 else p

theorem nonzero (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (tau witness : Fin n → ℕ) (i : Fin n) :
    polynomial q D tau witness i ≠ 0 := by
  dsimp only [polynomial]
  split_ifs with hz
  · exact one_ne_zero
  · intro hp
    exact hz (hp ▸ Polynomial.coeff_zero _)

/-- The table is bounded by the original Gram matrix dimension. Completeness
chooses true trailing slices; arbitrary other tables remain nonzero. -/
theorem exists_table (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) :
    ∃ tau witness : Fin n → ℕ,
      (∀ i, tau i ≤ CoerciveBoxGramEliminant.blockDimension n D ∧
        witness i ≤ CoerciveBoxGramEliminant.blockDimension n D) ∧
      ∀ i, polynomial q D tau witness i = CoerciveGramComponentGrid.head q D i := by
  let tau : Fin n → ℕ := fun i => (CoerciveBoxGramEliminant.polynomial q D i).natTrailingDegree
  let witness : Fin n → ℕ := fun i => (CoerciveGramComponentGrid.head q D i).natDegree
  have hw (i : Fin n) : ((CoerciveBoxGramEliminant.polynomial q D i).coeff (tau i)).coeff (witness i) ≠ 0 := by
    change (CoerciveGramComponentGrid.head q D i).coeff (CoerciveGramComponentGrid.head q D i).natDegree ≠ 0
    simpa only [Polynomial.coeff_natDegree] using
      Polynomial.leadingCoeff_ne_zero.mpr (CoerciveGramComponentGrid.head_ne_zero q D hD i)
  refine ⟨tau, witness, fun i => ⟨?_, ?_⟩, fun i => ?_⟩
  · exact (Polynomial.natTrailingDegree_le_natDegree _).trans (CoerciveBoxGramEliminant.outer_degree q D hD i)
  · exact CoerciveBoxGramEliminant.inner_degree q D hD i (tau i)
  · simp only [polynomial, hw i, ite_false]
    rfl

theorem joined_sample (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (x : Zeros (q.map (Int.castRingHom ℝ))) :
    ∃ tau witness : Fin n → ℕ,
      (∀ i, tau i ≤ CoerciveBoxGramEliminant.blockDimension n D ∧
        witness i ≤ CoerciveBoxGramEliminant.blockDimension n D) ∧
      ∃ a : Zeros (q.map (Int.castRingHom ℝ)),
        JoinedIn (Zeros (q.map (Int.castRingHom ℝ))) x.val a.val ∧
        ∀ i, (polynomial q D tau witness i).eval₂ (Int.castRingHom ℝ) (a.val i) = 0 := by
  obtain ⟨tau, witness, hb, he⟩ := exists_table q D hD
  obtain ⟨a, ha, hg⟩ := CoerciveGramComponentGrid.joined_sample q D hD x
  exact ⟨tau, witness, hb, a, ha, fun i => (he i).symm ▸ hg i⟩

end LeanCanny.Geometry.CoerciveGramWitnessGrid
