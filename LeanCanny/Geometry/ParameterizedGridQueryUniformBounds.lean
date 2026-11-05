/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ParameterizedGridQueryMass

/-! # Common degree ceilings for actual Cartesian-grid queries

A common input degree ceiling gives a common width and sign cutoff without
computing the actual degree of each member of the query family.
-/

@[expose] public section
namespace LeanCanny.Geometry.ParameterizedGridQuerySign
open LeanCanny.Algebra Polynomial
open scoped Classical BigOperators

def commonWidth (n D E : ℕ) := (n * D + E + 1).size

theorem width_le {n : ℕ} (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (D E : ℕ) (hp : ∀ i, (p i).natDegree ≤ D) (hq : q.totalDegree ≤ E) :
    RelativeAffineGridValueGram.width (fun i => (p i).natDegree) (q.totalDegree + 1) ≤
      commonWidth n D E := by
  apply Nat.size_le_size
  unfold Macaulay.level RelativeProjectiveValueGram.degrees
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, Nat.add_sub_cancel]
  have hs : (∑ i : Fin n, ((p i).natDegree - 1)) ≤ n * D := by
    calc
      _ ≤ ∑ _i : Fin n, D := Finset.sum_le_sum (fun i _ => (Nat.sub_le _ _).trans (hp i))
      _ = _ := by simp
  omega

theorem massBudget_mono_width {n W V H : ℕ} (h : W ≤ V) :
    massBudget n W H ≤ massBudget n V H := by
  have hL : FixedWidthPolynomial.count (n + 1) W ≤ FixedWidthPolynomial.count (n + 1) V :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) h) _
  unfold massBudget
  exact Nat.mul_le_mul hL (Nat.add_le_add_left
    (Nat.mul_le_mul_left 2 (Nat.size_le_size hL)) _)

theorem commonWidth_unary {n D E : List Bool → ℕ}
    (hn : UnaryFn n) (hd : BinaryFn D) (he : BinaryFn E) :
    UnaryFn (fun c => commonWidth (n c) (D c) (E c)) := by
  have hb := (((BinaryFn.ofUnary hn).mul hd).add he).add (BinaryFn.const 1)
  exact (UnaryFn.length hb.bits_mem_FP).of_eq (fun c => Nat.size_eq_bits_len _)

theorem commonCutoff_binary {n D E H : List Bool → ℕ}
    (hn : UnaryFn n) (hd : BinaryFn D) (he : BinaryFn E) (hh : BinaryFn H) :
    BinaryFn (fun c => cutoffBudget (n c) (commonWidth (n c) (D c) (E c)) (H c)) :=
  cutoffBudget_binary hn (commonWidth_unary hn hd he) hh

theorem sign_after_common_input_bounds {n : ℕ} {a b : ℝ}
    (p : Fin n → (ℤ[X])[X]) (q : MvPolynomial (Fin n) ℤ[X])
    (hpos : ∀ i, 0 < (p i).natDegree) (D E H : ℕ)
    (hd : ∀ i, (p i).natDegree ≤ D) (he : q.totalDegree ≤ E)
    (hp : ∀ i k, coefficientMass ((p i).coeff k) ≤ 2 ^ H)
    (hq : ∀ v, coefficientMass (q.coeff v) ≤ 2 ^ H)
    (ha : (2 : ℝ) ^ cutoffBudget n (commonWidth n D E) H ≤ a)
    (x : C(Set.Ioo a b, Fin n → ℝ))
    (hx : ∀ t i, (p i).eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (x t i) = 0)
    (s t : Set.Ioo a b) :
    SignType.sign (q.eval₂ (SymbolicScaledSquarefree.scalarEvaluation s.val) (x s)) =
      SignType.sign (q.eval₂ (SymbolicScaledSquarefree.scalarEvaluation t.val) (x t)) := by
  have hw := width_le p q D E hd he
  have hL : FixedWidthPolynomial.count (n + 1)
      (RelativeAffineGridValueGram.width (fun i => (p i).natDegree) (q.totalDegree + 1)) ≤
      FixedWidthPolynomial.count (n + 1) (commonWidth n D E) :=
    Nat.pow_le_pow_left (Nat.pow_le_pow_right (by decide) hw) _
  apply sign_transport p q _ x hx s t
  apply ParameterizedRootQuerySign.avoids_after_input_bounds (annihilator p q)
    (annihilator_ne_zero_of_mass p q hpos H hp) (fun _ : Unit => Polynomial.X)
    (RelativeProjectiveValueGram.dimension n (commonWidth n D E) + 1)
    (massBudget n (commonWidth n D E) H)
  · exact (RelativeAffineGridValueGram.degree_le p q _ _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left _ hL) 1)
  · intro j
    rw [Polynomial.natDegree_X]
    omega
  · intro k
    exact (NestedMass.coeff_le _ k).trans ((annihilator_mass p q H hp hq).trans
      (Nat.pow_le_pow_right (by decide) (massBudget_mono_width hw)))
  · intro j k
    simp only [Polynomial.coeff_X]
    split_ifs
    · change coefficientMass (Polynomial.C (1 : ℤ)) ≤ _
      rw [coefficientMass_C, Int.natAbs_one]
      exact Nat.one_le_two_pow
    · simp
  · exact ha

end LeanCanny.Geometry.ParameterizedGridQuerySign
