/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalHomogenization

/-! # Free coordinate blocks of pure-power-leading polynomials

Freezing the other coordinates preserves the free pure powers. The frozen
pure powers contribute only a constant to the lower part. Thus every block
contained in the original coordinates has the same leading degree; degree
bounds need no bounds on the values of the frozen coordinates.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinateBlockSpecialization
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S]

noncomputable def coordinate (frozen : ℕ → S) (offset dim i : ℕ) : MvPolynomial (Fin dim) S :=
  if hi : offset ≤ i ∧ i < offset + dim then X ⟨i - offset, by omega⟩ else C (frozen i)

noncomputable def specialize (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ) :
    MvPolynomial ℕ R →+* MvPolynomial (Fin dim) S :=
  eval₂Hom (C.comp φ) (coordinate frozen offset dim)

noncomputable def finite {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ) :
    MvPolynomial (Fin n) R →+* MvPolynomial (Fin dim) S :=
  eval₂Hom (C.comp φ) (fun i => coordinate frozen offset dim i.val)

theorem eval_finite {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (y : Fin dim → S) :
    (finite φ frozen offset dim p).eval y = p.eval₂ φ
      (fun i => if hi : offset ≤ i.val ∧ i.val < offset + dim then y ⟨i.val - offset, by omega⟩ else frozen i.val) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finite]
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval_mul, eval₂_mul, hp, eval₂_X]
    congr 1
    by_cases hi : offset ≤ i.val ∧ i.val < offset + dim <;> simp [finite, coordinate, hi]

theorem specialize_rename {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) :
    specialize φ frozen offset dim (rename Fin.val p) = finite φ frozen offset dim p := by
  change (rename Fin.val p).eval₂ (C.comp φ) (coordinate frozen offset dim) = _
  rw [eval₂_rename]
  rfl

theorem finite_congr {n : ℕ} (φ : R →+* S) (frozen parent : ℕ → S) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (h : ∀ i < n, frozen i = parent i) :
    finite φ frozen offset dim p = finite φ parent offset dim p := by
  have hv : (fun i : Fin n => coordinate frozen offset dim i.val) =
      (fun i : Fin n => coordinate parent offset dim i.val) := by
    funext i
    unfold coordinate
    split_ifs
    · rfl
    · rw [h i.val i.isLt]
  unfold finite
  rw [hv]

theorem finite_all {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (p : MvPolynomial (Fin n) R) :
    finite φ frozen 0 n p = p.map φ := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finite]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [finite, coordinate]

theorem finite_frozen {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (h : n ≤ offset) :
    finite φ frozen offset dim p = C (p.eval₂ φ (fun i => frozen i.val)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finite]
  | add p q hp hq => simp only [map_add, hp, hq, eval₂_add]
  | mul_X p i hp =>
    have hi : ¬ (offset ≤ i.val ∧ i.val < offset + dim) := by have := i.isLt; omega
    simp only [map_mul, hp, eval₂_mul, eval₂_X]
    congr 1
    simp only [finite, eval₂Hom_X', coordinate, dite_eq_right hi]

theorem coordinate_degree [Nontrivial S] (frozen : ℕ → S) (offset dim i : ℕ) :
    (coordinate frozen offset dim i).totalDegree ≤ 1 := by
  unfold coordinate
  split_ifs <;> simp

theorem finite_degree [Nontrivial S] {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) : (finite φ frozen offset dim p).totalDegree ≤ p.totalDegree := by
  change (p.eval₂ (C.comp φ) (fun i => coordinate frozen offset dim i.val)).totalDegree ≤ _
  rw [MvPolynomial.eval₂_eq]
  apply totalDegree_finsetSum_le
  intro e he
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.comp_apply, totalDegree_C, Nat.zero_add]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans _ (le_totalDegree he)
  apply Finset.sum_le_sum
  intro i _
  exact (totalDegree_pow _ _).trans (by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (e i) (coordinate_degree frozen offset dim i.val))

noncomputable def frozenPower {n : ℕ} (frozen : ℕ → S) (offset dim N : ℕ) : S :=
  ∑ i : Fin n, if offset ≤ i.val ∧ i.val < offset + dim then 0 else frozen i.val ^ N

theorem sum_free {n : ℕ} (offset dim N : ℕ) (hfit : offset + dim ≤ n) :
    (∑ i : Fin n, if hi : offset ≤ i.val ∧ i.val < offset + dim then
      (X ⟨i.val - offset, by omega⟩ : MvPolynomial (Fin dim) S) ^ N else 0) =
        ∑ j : Fin dim, X j ^ N := by
  let e : Fin dim → Fin n := fun j => ⟨offset + j.val, by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    have H := congrArg Fin.val hij
    dsimp only [e] at H
    omega
  apply (Fintype.sum_of_injective e he (fun j => (X j : MvPolynomial (Fin dim) S) ^ N)
    (fun i => if hi : offset ≤ i.val ∧ i.val < offset + dim then
      (X ⟨i.val - offset, by omega⟩ : MvPolynomial (Fin dim) S) ^ N else 0) ?_ ?_).symm
  · intro i hi
    have hout : ¬ (offset ≤ i.val ∧ i.val < offset + dim) := by
      intro hin
      apply hi
      refine ⟨⟨i.val - offset, by omega⟩, Fin.ext ?_⟩
      dsimp only [e]
      omega
    exact dite_eq_right hout
  · intro j
    have hin : offset ≤ (e j).val ∧ (e j).val < offset + dim := by dsimp [e]; omega
    rw [dite_eq_left hin]
    congr 2
    exact Fin.ext (by dsimp [e]; omega)

theorem sum_powers {n : ℕ} (frozen : ℕ → S) (offset dim N : ℕ) (hfit : offset + dim ≤ n) :
    (∑ i : Fin n, coordinate frozen offset dim i.val ^ N) =
      (∑ j : Fin dim, X j ^ N) + C (frozenPower (n := n) frozen offset dim N) := by
  have hv (i : Fin n) : coordinate frozen offset dim i.val ^ N =
      (if hi : offset ≤ i.val ∧ i.val < offset + dim then X ⟨i.val - offset, by omega⟩ ^ N else 0) +
        C (if offset ≤ i.val ∧ i.val < offset + dim then 0 else frozen i.val ^ N) := by
    unfold coordinate
    split_ifs <;> simp
  simp only [hv, Finset.sum_add_distrib, ← map_sum]
  rw [sum_free offset dim N hfit]
  rfl

noncomputable def lower {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ)
    (low : MvPolynomial (Fin n) R) (a : R) (N : ℕ) : MvPolynomial (Fin dim) S :=
  finite φ frozen offset dim low + C (φ a * frozenPower (n := n) frozen offset dim N)

theorem finite_fermat {n k : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset : ℕ)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (N : ℕ) (hfit : offset + (k + 1) ≤ n + 1) :
    finite φ frozen offset (k + 1) (FermatCriticalHomogenization.polynomial low a N) =
      FermatCriticalHomogenization.polynomial (lower φ frozen offset (k + 1) low a N) (φ a) N := by
  have hs := sum_powers frozen offset (k + 1) N hfit
  simp only [FermatCriticalHomogenization.polynomial, lower, map_add, map_mul, map_sum, map_pow,
    finite, eval₂Hom_C, RingHom.comp_apply, eval₂Hom_X']
  rw [hs]
  ring

theorem lower_degree [Nontrivial S] {n : ℕ} (φ : R →+* S) (frozen : ℕ → S) (offset dim : ℕ)
    (low : MvPolynomial (Fin n) R) (a : R) (N : ℕ) (hlow : low.totalDegree < N) :
    (lower φ frozen offset dim low a N).totalDegree < N := by
  apply (totalDegree_add _ _).trans_lt
  exact max_lt ((finite_degree φ frozen offset dim low).trans_lt hlow) (by rw [totalDegree_C]; omega)

end LeanCanny.Algebra.CoordinateBlockSpecialization
