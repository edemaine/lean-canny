/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RowSpanSpecialization
public import LeanCanny.Algebra.MacaulayProjectiveCriterion
public import LeanCanny.Algebra.MacaulayMaximalMinors
public import LeanCanny.Algebra.CoefficientBounds

/-! # Bounded sweep samples certifying generic projective root-freeness

A root-free generic fiber has a nonzero maximal Macaulay minor of bounded
parameter degree. Some bounded integer sweep value avoids that minor.
Conversely, a single root-free specialization certifies root-freeness after
any injective coefficient map, so the minor itself need not be stored.
-/

@[expose] public section
namespace LeanCanny.Algebra.ProjectiveSweepGrid
open MvPolynomial
open scoped Classical Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K F L : Type*} [Field K] [CharZero K] [Field F] [Field L]

theorem exists_nat_eval_ne_zero (p : Polynomial K) (hp : p ≠ 0) (b : ℕ)
    (hb : p.natDegree ≤ b) : ∃ t : ℕ, t ≤ b ∧ p.eval (t : K) ≠ 0 := by
  by_contra hn
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun i : Fin (b + 1) => (i.val : K))
    (fun i j h => Fin.ext (Nat.cast_injective h))
  · intro i
    by_contra hi
    exact hn ⟨i.val, by omega, hi⟩
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hb

omit [CharZero K] in
private theorem full_entry_cases
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial K))
    (d : Fin (n + 1) → ℕ) (W : ℕ)
    (a : Macaulay.MultiplierIndex d W) (r : Macaulay.activeIndices d W) :
    Macaulay.fullMatrix p d W a r = 0 ∨
      ∃ e, Macaulay.fullMatrix p d W a r = (p a.1).coeff e := by
  unfold Macaulay.fullMatrix Macaulay.sourceRow
  rw [coeff_monomial_mul']
  split_ifs
  · exact Or.inr ⟨_, one_mul _⟩
  · exact Or.inl rfl

theorem exists_bounded [IsAlgClosed F]
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) (Polynomial K))
    (d : Fin (n + 1) → ℕ) (W E : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ j, (p j).IsHomogeneous (d j)) (hd : ∀ j, 0 < d j)
    (hE : ∀ j e, ((p j).coeff e).natDegree ≤ E) (φ : Polynomial K →+* F)
    (hroot : ∀ x : Fin (n + 1) → F, (∀ j, (p j).eval₂ φ x = 0) → x = 0) :
    ∃ t : ℕ, t ≤ FixedWidthPolynomial.count (n + 1) W * E ∧
      ∀ (L : Type*) [Field L] [Algebra K L] (x : Fin (n + 1) → L),
        (∀ j, (p j).eval₂ (Polynomial.eval₂RingHom (algebraMap K L) (t : L)) x = 0) → x = 0 := by
  have hs : Function.Surjective (fun v => Matrix.vecMul v ((Macaulay.fullMatrix p d W).map φ)) := by
    rw [Macaulay.fullMatrix_map]
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W (fun j => (hp j).map φ) hd hW
    intro x hx
    apply hroot x
    intro j
    simpa only [eval_map] using hx j
  obtain ⟨a, ha⟩ := RowSpanSpecialization.exists_nonzero_minor φ (Macaulay.fullMatrix p d W) hs
  let H := ((Macaulay.fullMatrix p d W).submatrix a id).det
  have hdeg : H.natDegree ≤ FixedWidthPolynomial.count (n + 1) W * E := by
    have hentry (i j : Macaulay.activeIndices d W) :
        (((Macaulay.fullMatrix p d W).submatrix a id) i j).natDegree ≤ E := by
      change (Macaulay.fullMatrix p d W (a i) j).natDegree ≤ E
      rcases full_entry_cases p d W (a i) j with hz | ⟨e, he⟩
      · simpa only [hz, Polynomial.natDegree_zero] using Nat.zero_le E
      · simpa only [he] using hE (a i).1 e
    have hb := det_natDegree_le ((Macaulay.fullMatrix p d W).submatrix a id) (fun _ => E) hentry
    apply hb.trans
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    apply Nat.mul_le_mul_right E
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      (Finset.card_le_univ (s := Macaulay.activeIndices d W))
  obtain ⟨t, ht, hHt⟩ := exists_nat_eval_ne_zero H ha _ hdeg
  refine ⟨t, ht, ?_⟩
  intro L _ _ x hx
  let ψ := Polynomial.eval₂RingHom (algebraMap K L) (t : L)
  have hH : ψ H ≠ 0 := by
    have he : ψ H = algebraMap K L (H.eval (t : K)) := by
      change Polynomial.eval₂ (algebraMap K L) (t : L) H = _
      simpa only [Polynomial.eval₂_id, RingHom.comp_id, map_natCast] using
        (Polynomial.hom_eval₂ H (RingHom.id K) (algebraMap K L) (t : K)).symm
    rw [he]
    exact fun hz => hHt ((algebraMap K L).injective (hz.trans (map_zero _).symm))
  by_contra hn
  have hnz : ∃ j, x j ≠ 0 := by simpa only [funext_iff, Pi.zero_apply, not_forall] using hn
  have hdegree := MacaulayUniversal.degree_lt_width d W hd hW
  obtain ⟨c, hc⟩ := MacaulayUniversal.polynomialValue_dvd_fullMinor d W hdegree hW p hp hd a
  apply hH
  change ψ (((Macaulay.fullMatrix p d W).submatrix a id).det) = 0
  rw [hc, map_mul,
    MacaulayUniversal.map_polynomialValue_eq_zero_of_common_root ψ d W hdegree hW p hp hd x hx hnz,
    zero_mul]

omit [CharZero K] in
/-- A root-free sample certifies every injective generic specialization. -/
theorem generic_of_sample [IsAlgClosed F]
    (p : Fin n → MvPolynomial (Fin n) (Polynomial K)) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (hp : ∀ j, (p j).IsHomogeneous (d j)) (hd : ∀ j, 0 < d j)
    (φ : Polynomial K →+* F)
    (hroot : ∀ x : Fin n → F, (∀ j, (p j).eval₂ φ x = 0) → x = 0)
    (ψ : Polynomial K →+* L) (hψ : Function.Injective ψ)
    (x : Fin n → L) (hx : ∀ j, (p j).eval₂ ψ x = 0) : x = 0 := by
  have hs : Function.Surjective (fun v => Matrix.vecMul v ((Macaulay.fullMatrix p d W).map φ)) := by
    rw [Macaulay.fullMatrix_map]
    apply Macaulay.fullMatrix_surjective_of_no_nonzero_root _ d W (fun j => (hp j).map φ) hd hW
    intro y hy
    apply hroot y
    intro j
    simpa only [eval_map] using hy j
  have hg := RowSpanSpecialization.generic_surjective φ ψ hψ (Macaulay.fullMatrix p d W) hs
  rw [Macaulay.fullMatrix_map] at hg
  apply Macaulay.no_nonzero_root_of_fullMatrix_surjective _ d W (fun j => (hp j).map ψ) hW hg x
  intro j
  simpa only [eval_map] using hx j

end LeanCanny.Algebra.ProjectiveSweepGrid
