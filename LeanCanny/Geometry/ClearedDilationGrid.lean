/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedDilationLimit
public import Mathlib.Algebra.Polynomial.Roots

/-! # Finite selected-parent grids for denominator-cleared dilation limits -/
@[expose] public section
namespace LeanCanny.Geometry.ClearedDilationGrid
open Polynomial Filter Set LeanCanny.Algebra
open scoped Topology
variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def candidate (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q : R)
    (i : Fin (p.natDegree+1)) : Polynomial ℝ :=
  ((Bivariate.swap (ClearedDilatedCoordinatePolynomial.rescale p q)).coeff i.val).map φ

theorem selected_candidate (φ : R →+* ℝ) (p : Polynomial (Polynomial R)) (q a : R)
    (ha : φ a≠0) (hd : p.coeff p.natDegree=C a) :
    ∃ i : Fin (p.natDegree+1), candidate φ p q i=ClearedDilationLimit.coordinate φ p q ∧
      candidate φ p q i≠0 ∧ (candidate φ p q i).natDegree ≤ p.natDegree := by
  let i : Fin (p.natDegree+1) :=
    ⟨(ClearedDilationLimit.selected φ p q).natTrailingDegree,by
      have H := ClearedDilationLimit.index_le φ p q a ha hd; omega⟩
  have HE : candidate φ p q i=ClearedDilationLimit.coordinate φ p q :=
    (ClearedDilationLimit.coordinate_eq_coefficient φ p q).symm
  exact ⟨i,HE,HE.symm ▸ ClearedDilationLimit.coordinate_ne_zero φ p q a ha hd,
    HE.symm ▸ ClearedDilationLimit.coordinate_degree φ p q a ha hd⟩

noncomputable def grid (φ : R →+* ℝ) (p : Fin n → Polynomial (Polynomial R)) (q : R) : Set (Fin n → ℝ) :=
  {x | ∀ j, (ClearedDilationLimit.coordinate φ (p j) q).eval (x j)=0}

theorem finite_grid (φ : R →+* ℝ) (p : Fin n → Polynomial (Polynomial R)) (q : R)
    (a : Fin n → R) (ha : ∀ j, φ (a j)≠0) (hd : ∀ j, (p j).coeff (p j).natDegree=C (a j)) :
    (grid φ p q).Finite :=
  Set.Finite.pi' (fun j => finite_setOfPred_isRoot (ClearedDilationLimit.coordinate_ne_zero φ (p j) q (a j) (ha j) (hd j)))

theorem limit_mem {I : Type*} (l : Filter I) [NeBot l]
    (φ : R →+* ℝ) (p : Fin n → Polynomial (Polynomial R)) (q : R)
    (eta : I → ℝ) (y x : I → Fin n → ℝ) (a : Fin n → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto x l (𝓝 a))
    (hne : ∀ᶠ i in l, eta i≠0)
    (hy : ∀ᶠ i in l, ∀ j, φ q*y i j=eta i*x i j)
    (hp : ∀ᶠ i in l, ∀ j, eval₂ (eval₂RingHom φ (eta i)) (y i j) (p j)=0) : a∈grid φ p q := by
  intro j
  exact ClearedDilationLimit.limit_root l φ (p j) q eta (fun i => y i j) (fun i => x i j) (a j)
    heta ((continuous_apply j).continuousAt.tendsto.comp hx) hne
    (hy.mono (fun _ H => H j)) (hp.mono (fun _ H => H j))

end LeanCanny.Geometry.ClearedDilationGrid
