/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MonicMonomialReduction
public import LeanCanny.Algebra.FixedWidthPolynomial
public import LeanCanny.Algebra.ScaledGradedReductionMatrix

/-! # A concrete finite matrix for pure-power-leading relations

Fixed-width exponent words index every state. Normal monomials have diagonal
c. Other valid columns replace the first divisible pure power by its lower
part. Oversized columns are zero and carry evaluation zero. Every nonnormal
transition decreases total degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionMatrix
open MvPolynomial Matrix MonicMonomialReduction
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n B : ℕ} {R : Type*} [CommRing R]

abbrev Index (n B : ℕ) := Fin (FixedWidthPolynomial.count n B)

def Normal (d : Fin n → ℕ) (e : Fin n →₀ ℕ) : Prop := ∀ i, e i < d i

noncomputable def candidates (d : Fin n → ℕ) (e : Fin n →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => d i ≤ e i)

noncomputable def selected (fallback : Fin n) (d : Fin n → ℕ) (e : Fin n →₀ ℕ) : Fin n :=
  if h : (candidates d e).Nonempty then (candidates d e).min' h else fallback

theorem selected_divides (fallback : Fin n) (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : ¬Normal d e) :
    d (selected fallback d e) ≤ e (selected fallback d e) := by
  have hne : (candidates d e).Nonempty := by
    have H : ∃ i, d i ≤ e i := by simpa only [Normal, not_forall, not_lt] using he
    obtain ⟨i, hi⟩ := H
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  rw [selected, dite_eq_left hne]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2

noncomputable def degree (bound : ℕ) (j : Index n B) : ℕ :=
  if (FixedWidthPolynomial.vector n B j).degree ≤ bound then (FixedWidthPolynomial.vector n B j).degree else 0

theorem degree_le (bound : ℕ) (j : Index n B) : degree bound j ≤ bound := by
  unfold degree
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

noncomputable def matrix (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (c : R) (bound : ℕ) : Matrix (Index n B) (Index n B) R := fun i j =>
  let e := FixedWidthPolynomial.vector n B j
  if Normal d e then (if i = j then c else 0)
  else if e.degree ≤ bound then
    (step (low (selected fallback d e)) e (selected fallback d e) (d (selected fallback d e))).coeff
      (FixedWidthPolynomial.vector n B i)
  else 0

theorem normal_column (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (c : R) (bound : ℕ) (j : Index n B) (hj : Normal d (FixedWidthPolynomial.vector n B j)) (i : Index n B) :
    matrix fallback d low c bound i j = if i = j then c else 0 := by
  simp only [matrix, ite_eq_left hj]

theorem decreases (fallback : Fin n) (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R)
    (hlow : ∀ i, (low i).totalDegree < d i) (c : R) (bound : ℕ) (i j : Index n B)
    (hj : ¬Normal d (FixedWidthPolynomial.vector n B j)) (hT : matrix fallback d low c bound i j ≠ 0) :
    degree bound i < degree bound j := by
  by_cases hvalid : (FixedWidthPolynomial.vector n B j).degree ≤ bound
  · let e := FixedWidthPolynomial.vector n B j
    let r := selected fallback d e
    have Hr : d r ≤ e r := selected_divides fallback d e hj
    have HP := step_degree (low r) e r (d r) Hr (hlow r)
    have HC : (step (low r) e r (d r)).coeff (FixedWidthPolynomial.vector n B i) ≠ 0 := by
      simpa only [matrix, ite_eq_right hj, ite_eq_left hvalid] using hT
    have HM := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr HC)
    have HM' : (FixedWidthPolynomial.vector n B i).degree ≤ (step (low r) e r (d r)).totalDegree := by
      simpa only [Finsupp.degree_apply, Finsupp.sum] using HM
    have HI : (FixedWidthPolynomial.vector n B i).degree < (FixedWidthPolynomial.vector n B j).degree :=
      HM'.trans_lt HP
    have hi : (FixedWidthPolynomial.vector n B i).degree ≤ bound := HI.le.trans hvalid
    simpa only [degree, ite_eq_left hi, ite_eq_left hvalid] using HI
  · exact False.elim (hT (by simp only [matrix, ite_eq_right hj, ite_eq_right hvalid]))

noncomputable def evaluation {K : Type*} [CommRing K] (φ : R →+* K) (bound : ℕ)
    (x : Fin n → K) (i : Index n B) : K :=
  if (FixedWidthPolynomial.vector n B i).degree ≤ bound then
    (monomial (FixedWidthPolynomial.vector n B i) (1 : R)).eval₂ φ x else 0

theorem evaluation_sum {K : Type*} [CommRing K] (φ : R →+* K) (bound : ℕ) (hbound : bound < 2 ^ B)
    (x : Fin n → K) (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ bound) :
    (∑ i : Index n B, evaluation φ bound x i * φ (p.coeff (FixedWidthPolynomial.vector n B i))) = p.eval₂ φ x := by
  have HS := FixedWidthPolynomial.sum_monomials_eq n B p (fun e he i =>
    (Finsupp.le_degree i e).trans_lt ((MvPolynomial.le_totalDegree he).trans_lt (hp.trans_lt hbound)))
  have HE := congrArg (fun p : MvPolynomial (Fin n) R => p.eval₂ φ x) HS
  calc
    _ = ∑ i : Index n B, (monomial (FixedWidthPolynomial.vector n B i) (1 : R)).eval₂ φ x *
        φ (p.coeff (FixedWidthPolynomial.vector n B i)) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : (FixedWidthPolynomial.vector n B i).degree ≤ bound
      · rw [evaluation, ite_eq_left hi]
      · have HC : p.coeff (FixedWidthPolynomial.vector n B i) = 0 := by
          by_contra h
          exact hi ((MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr h)).trans hp)
        rw [HC, map_zero, mul_zero, mul_zero]
    _ = p.eval₂ φ x := by
      simpa only [eval₂_sum, eval₂_monomial, map_one, one_mul, mul_comm] using HE

theorem evaluation_relation {K : Type*} [CommRing K] (φ : R →+* K) (fallback : Fin n)
    (d : Fin n → ℕ) (low : Fin n → MvPolynomial (Fin n) R) (hlow : ∀ i, (low i).totalDegree < d i)
    (c : R) (bound : ℕ) (hbound : bound < 2 ^ B) (x : Fin n → K)
    (hx : ∀ i, (C c * X i ^ d i + low i).eval₂ φ x = 0) :
    evaluation (B := B) φ bound x ᵥ* (matrix (B := B) fallback d low c bound).map φ =
      φ c • evaluation (B := B) φ bound x := by
  funext j
  change (∑ i : Index n B, evaluation φ bound x i * φ (matrix fallback d low c bound i j)) =
    φ c * evaluation φ bound x j
  by_cases hj : Normal d (FixedWidthPolynomial.vector n B j)
  · rw [Finset.sum_eq_single j]
    · rw [normal_column fallback d low c bound j hj j, ite_eq_left rfl]
      exact mul_comm _ _
    · intro i _ hij
      rw [normal_column fallback d low c bound j hj i, ite_eq_right hij, map_zero, mul_zero]
    · simp
  · by_cases hvalid : (FixedWidthPolynomial.vector n B j).degree ≤ bound
    · let e := FixedWidthPolynomial.vector n B j
      let r := selected fallback d e
      let P := step (low r) e r (d r)
      have Hr : d r ≤ e r := selected_divides fallback d e hj
      have HP : P.totalDegree ≤ bound := (step_degree (low r) e r (d r) Hr (hlow r)).le.trans hvalid
      calc
        _ = P.eval₂ φ x := by
          simpa only [matrix, ite_eq_right hj, ite_eq_left hvalid] using evaluation_sum φ bound hbound x P HP
        _ = φ c * (monomial e (1 : R)).eval₂ φ x := step_eval φ (low r) e r (d r) Hr c x (hx r)
        _ = φ c * evaluation φ bound x j := by rw [evaluation, ite_eq_left hvalid]
    · simp only [matrix, ite_eq_right hj, ite_eq_right hvalid, map_zero, mul_zero,
        Finset.sum_const_zero, evaluation]

end LeanCanny.Algebra.PurePowerReductionMatrix
