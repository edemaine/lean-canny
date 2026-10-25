/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RowSpanSpecialization
public import LeanCanny.Algebra.MacaulayProjectiveCriterion
public import LeanCanny.Algebra.MacaulayMaximalMinors
public import LeanCanny.Algebra.PolynomialGridAvoidance

/-! # A bounded integer grid preserving a root-free projective system

One root-free specialization selects a nonzero maximal Macaulay minor. Its
parameter degree is at most the column count times the entry degree. An
integer grid of that allowance therefore contains a specialization retaining
projective root-freeness over every extension of the coefficient field.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveDirectionGrid
open MvPolynomial
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {K F : Type*} [Field K] [CharZero K] [Field F] [IsAlgClosed F]

theorem allowance_size_le (n W E : ℕ) :
    (FixedWidthPolynomial.count (n + 1) W * E).size ≤ (n + 1) * W + E.size := by
  apply Nat.size_le.mpr
  unfold FixedWidthPolynomial.count
  rw [← pow_mul, Nat.mul_comm W (n + 1), pow_add]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self E) (pow_pos (by decide) _)

omit [CharZero K] in
private theorem full_entry_cases
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m) K))
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (a : Macaulay.MultiplierIndex d W) (r : Macaulay.activeIndices d W) :
    Macaulay.fullMatrix p d W a r = 0 ∨
      ∃ e, Macaulay.fullMatrix p d W a r = (p a.1).coeff e := by
  unfold Macaulay.fullMatrix Macaulay.sourceRow
  rw [coeff_monomial_mul']
  split_ifs
  · exact Or.inr ⟨_, one_mul _⟩
  · exact Or.inl rfl

omit [CharZero K] in
private theorem det_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial (Fin m) K)) (E : ℕ)
    (hE : ∀ i j, (A i j).totalDegree ≤ E) : A.det.totalDegree ≤ Fintype.card ι * E := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro σ _
  rw [Units.smul_def]
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun j _ => hE (σ j) j).trans_eq (by simp)

/-- The direction allowance is computed from the matrix width and the source
parameter degree, rather than the degree of a supplied exceptional factor. -/
theorem exists_bounded
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m) K))
    (d : Fin (n + 1) → ℕ) (W E : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ j, (p j).IsHomogeneous (d j)) (hd : ∀ j, 0 < d j)
    (hE : ∀ j e, ((p j).coeff e).totalDegree ≤ E)
    (φ : MvPolynomial (Fin m) K →+* F)
    (hroot : ∀ x : Fin (n + 1) → F, (∀ j, (p j).eval₂ φ x = 0) → x = 0) :
    ∃ u : Fin m → ℕ, (∀ i, u i ≤ FixedWidthPolynomial.count (n + 1) W * E) ∧
      ∀ (L : Type*) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (p j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (u i : L))) x = 0) → x = 0 := by
  have hs : Function.Surjective (fun v => Matrix.vecMul v ((Macaulay.fullMatrix p d W).map φ)) := by
    rw [Macaulay.fullMatrix_map]
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W (fun j => (hp j).map φ) hd hW
    intro x hx
    apply hroot x
    intro j
    simpa only [eval_map] using hx j
  obtain ⟨a, ha⟩ := RowSpanSpecialization.exists_nonzero_minor φ (Macaulay.fullMatrix p d W) hs
  let H := ((Macaulay.fullMatrix p d W).submatrix a id).det
  have hdeg : H.totalDegree ≤ FixedWidthPolynomial.count (n + 1) W * E := by
    have hentry (i j : Macaulay.activeIndices d W) :
        (((Macaulay.fullMatrix p d W).submatrix a id) i j).totalDegree ≤ E := by
      change (Macaulay.fullMatrix p d W (a i) j).totalDegree ≤ E
      rcases full_entry_cases p d W (a i) j with hz | ⟨e, he⟩
      · simpa only [hz, totalDegree_zero] using Nat.zero_le E
      · simpa only [he] using hE (a i).1 e
    exact (det_degree _ E hentry).trans (Nat.mul_le_mul_right E (by
        simpa only [Fintype.card_coe, Fintype.card_fin] using
          (Finset.card_le_univ (s := Macaulay.activeIndices d W))))
  obtain ⟨u, hu, hHu⟩ := PolynomialGridAvoidance.exists_nat_eval_ne_zero H ha
    (FixedWidthPolynomial.count (n + 1) W * E) hdeg
  refine ⟨u, hu, ?_⟩
  intro L _ _ x hx
  let ψ := eval₂Hom (algebraMap K L) (fun i => (u i : L))
  have hcomp : ψ = (algebraMap K L).comp (eval (fun i => (u i : K))) := by
    ext <;> simp [ψ]
  have hH : ψ H ≠ 0 := by
    rw [hcomp]
    intro hz
    apply hHu
    apply (algebraMap K L).injective
    simpa only [RingHom.comp_apply, map_zero] using hz
  by_contra hn
  have hnz : ∃ j, x j ≠ 0 := by
    simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
  have hdegree := MacaulayUniversal.degree_lt_width d W hd hW
  obtain ⟨c, hc⟩ := MacaulayUniversal.polynomialValue_dvd_fullMinor d W hdegree hW p hp hd a
  have hzero : ψ H = 0 := by
    change ψ (((Macaulay.fullMatrix p d W).submatrix a id).det) = 0
    rw [hc, map_mul,
      MacaulayUniversal.map_polynomialValue_eq_zero_of_common_root ψ d W hdegree hW p hp hd x hx hnz,
      zero_mul]
  exact hH hzero

end LeanCanny.Algebra.ProjectiveDirectionGrid
