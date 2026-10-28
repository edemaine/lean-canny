/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectiveDirectionGrid

/-! # One bounded integer direction for a finite projective family

Each generically root-free homogeneous system supplies a nonzero maximal
Macaulay minor of bounded parameter degree. Avoiding all these minors at once
costs a factor equal to the family cardinality in the integer grid allowance.
The retained systems stay root-free over all coefficient-field extensions.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveDirectionFamily
open MvPolynomial
open scoped Classical BigOperators Matrix
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ} {K F : Type*} [Field K] [Field F] [IsAlgClosed F]

private theorem det_degree {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (MvPolynomial (Fin m) K)) (E : ℕ)
    (hE : ∀ i j, (A i j).totalDegree ≤ E) : A.det.totalDegree ≤ Fintype.card ι * E := by
  rw [Matrix.det_apply]
  apply totalDegree_finsetSum_le
  intro π _
  rw [Units.smul_def]
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  exact (Finset.sum_le_sum fun j _ => hE (π j) j).trans_eq (by simp)

theorem exists_certificate
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m) K))
    (d : Fin (n + 1) → ℕ) (W E : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ j, (p j).IsHomogeneous (d j)) (hd : ∀ j, 0 < d j)
    (hE : ∀ j e, ((p j).coeff e).totalDegree ≤ E)
    (φ : MvPolynomial (Fin m) K →+* F)
    (hroot : ∀ x : Fin (n + 1) → F, (∀ j, (p j).eval₂ φ x = 0) → x = 0) :
    ∃ H : MvPolynomial (Fin m) K, H ≠ 0 ∧ H.totalDegree ≤ FixedWidthPolynomial.count (n + 1) W * E ∧
      ∀ (L : Type*) [Field L] (ψ : MvPolynomial (Fin m) K →+* L), ψ H ≠ 0 →
        ∀ x : Fin (n + 1) → L, (∀ j, (p j).eval₂ ψ x = 0) → x = 0 := by
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
      unfold Macaulay.fullMatrix Macaulay.sourceRow
      rw [coeff_monomial_mul']
      split_ifs
      · simpa only [one_mul] using hE (a i).1 _
      · simpa only [totalDegree_zero] using Nat.zero_le E
    exact (det_degree _ E hentry).trans (Nat.mul_le_mul_right E (by
      simpa only [Fintype.card_coe, Fintype.card_fin] using
        (Finset.card_le_univ (s := Macaulay.activeIndices d W))))
  refine ⟨H, ha, hdeg, ?_⟩
  intro L _ ψ hH x hx
  by_contra hn
  have hnz : ∃ j, x j ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
  have hdegree := MacaulayUniversal.degree_lt_width d W hd hW
  obtain ⟨c, hc⟩ := MacaulayUniversal.polynomialValue_dvd_fullMinor d W hdegree hW p hp hd a
  apply hH
  change ψ (((Macaulay.fullMatrix p d W).submatrix a id).det) = 0
  rw [hc, map_mul,
    MacaulayUniversal.map_polynomialValue_eq_zero_of_common_root ψ d W hdegree hW p hp hd x hx hnz,
    zero_mul]

theorem exists_common_bounded [CharZero K] {σ : Type*} [Fintype σ]
    (p : σ → Fin (n + 1) → MvPolynomial (Fin (n + 1)) (MvPolynomial (Fin m) K))
    (d : Fin (n + 1) → ℕ) (W E : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ s j, (p s j).IsHomogeneous (d j)) (hd : ∀ j, 0 < d j)
    (hE : ∀ s j e, ((p s j).coeff e).totalDegree ≤ E)
    (φ : MvPolynomial (Fin m) K →+* F)
    (hroot : ∀ s, ∀ x : Fin (n + 1) → F, (∀ j, (p s j).eval₂ φ x = 0) → x = 0) :
    ∃ u : Fin m → ℕ, (∀ i, u i ≤ Fintype.card σ * (FixedWidthPolynomial.count (n + 1) W * E)) ∧
      ∀ s, ∀ (L : Type*) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (p s j).eval₂ (eval₂Hom (algebraMap K L) (fun i => (u i : L))) x = 0) → x = 0 := by
  choose H hH hdeg hkeep using fun s => exists_certificate (p s) d W E hW (hp s) hd (hE s) φ (hroot s)
  have hsum : ∑ s, (H s).totalDegree ≤ Fintype.card σ * (FixedWidthPolynomial.count (n + 1) W * E) :=
    (Finset.sum_le_sum fun s _ => hdeg s).trans_eq (by simp)
  obtain ⟨u, hu, hHu⟩ := PolynomialGridAvoidance.exists_nat_common_nonzero H hH _ hsum
  refine ⟨u, hu, ?_⟩
  intro s L _ _ x hx
  let ψ := eval₂Hom (algebraMap K L) (fun i => (u i : L))
  have hcomp : ψ = (algebraMap K L).comp (eval (fun i => (u i : K))) := by
    ext <;> simp [ψ]
  apply hkeep s L ψ ?_ x hx
  rw [hcomp]
  intro hz
  apply hHu s
  apply (algebraMap K L).injective
  simpa only [RingHom.comp_apply, map_zero] using hz

end LeanCanny.Algebra.ProjectiveDirectionFamily
