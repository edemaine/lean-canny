/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationDegree
public import LeanCanny.Algebra.IndexedRationalSubstitution

/-!
# Indexed monomials of an ETR expression tree

Addition concatenates source term families; multiplication flattens their
Cartesian product by quotient and remainder. The representation keeps repeated
monomials, zero coefficients, and cancellations. Its reference sum is exactly
the original multivariate polynomial. The recursive readers specify one term
at a time and never construct the expanded list.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open scoped BigOperators

def monomialCount : Term → ℕ
  | .const _ | .var _ => 1
  | .add a b => a.monomialCount + b.monomialCount
  | .mul a b => a.monomialCount * b.monomialCount

theorem monomialCount_pos (t : Term) : 0 < t.monomialCount := by
  induction t with
  | const _ | var _ => simp only [monomialCount, Nat.zero_lt_one]
  | add a b ha hb => exact Nat.add_pos_left ha _
  | mul a b ha hb => exact Nat.mul_pos ha hb

def monomialCoefficient : Term → ℕ → ℤ
  | .const z, _ => z
  | .var _, _ => 1
  | .add a b, r => if r < a.monomialCount then a.monomialCoefficient r else b.monomialCoefficient (r - a.monomialCount)
  | .mul a b, r => a.monomialCoefficient (r / b.monomialCount) * b.monomialCoefficient (r % b.monomialCount)

def monomialExponent : Term → ℕ → ℕ → ℕ
  | .const _, _, _ => 0
  | .var j, _, i => if i = j then 1 else 0
  | .add a b, r, i => if r < a.monomialCount then a.monomialExponent r i else b.monomialExponent (r - a.monomialCount) i
  | .mul a b, r, i => a.monomialExponent (r / b.monomialCount) i + b.monomialExponent (r % b.monomialCount) i

noncomputable def monomialPowers : Term → ℕ → (ℕ →₀ ℕ)
  | .const _, _ => 0
  | .var j, _ => Finsupp.single j 1
  | .add a b, r => if r < a.monomialCount then a.monomialPowers r else b.monomialPowers (r - a.monomialCount)
  | .mul a b, r => a.monomialPowers (r / b.monomialCount) + b.monomialPowers (r % b.monomialCount)

theorem monomialPowers_apply (t : Term) (r i : ℕ) : t.monomialPowers r i = t.monomialExponent r i := by
  induction t generalizing r with
  | const z => rfl
  | var j => simp only [monomialPowers, monomialExponent, Finsupp.single_apply, eq_comm]
  | add a b ha hb =>
    simp only [monomialPowers, monomialExponent]
    split_ifs <;> simp only [ha, hb]
  | mul a b ha hb => simp only [monomialPowers, monomialExponent, Finsupp.add_apply, ha, hb]

noncomputable def indexedMonomial (t : Term) (r : ℕ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.monomial (t.monomialPowers r) (t.monomialCoefficient r)

theorem indexedMonomial_add_left (a b : Term) (r : ℕ) (hr : r < a.monomialCount) :
    (a.add b).indexedMonomial r = a.indexedMonomial r := by
  simp only [indexedMonomial, monomialPowers, monomialCoefficient, hr, ↓reduceIte]

theorem indexedMonomial_add_right (a b : Term) (r : ℕ) :
    (a.add b).indexedMonomial (a.monomialCount + r) = b.indexedMonomial r := by
  have hr : ¬ a.monomialCount + r < a.monomialCount := by omega
  simp only [indexedMonomial, monomialPowers, monomialCoefficient, hr, ↓reduceIte, Nat.add_sub_cancel_left]

theorem indexedMonomial_mul (a b : Term) (r : ℕ) :
    (a.mul b).indexedMonomial r =
      a.indexedMonomial (r / b.monomialCount) * b.indexedMonomial (r % b.monomialCount) := by
  simp only [indexedMonomial, monomialPowers, monomialCoefficient, MvPolynomial.monomial_mul_monomial]

theorem sum_range_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) (A B : ℕ) :
    (∑ r ∈ Finset.range (A * B), f r) = ∑ i ∈ Finset.range A, ∑ j ∈ Finset.range B, f (i * B + j) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem indexedMonomial_sum (t : Term) :
    (∑ r ∈ Finset.range t.monomialCount, t.indexedMonomial r) = t.toPolynomial := by
  induction t with
  | const z => simp [monomialCount, indexedMonomial, monomialPowers, monomialCoefficient, toPolynomial, MvPolynomial.monomial_zero']
  | var i => simp [monomialCount, indexedMonomial, monomialPowers, monomialCoefficient, toPolynomial, MvPolynomial.X]
  | add a b ha hb =>
    rw [monomialCount, Finset.sum_range_add, toPolynomial, ← ha, ← hb]
    congr 1
    · exact Finset.sum_congr rfl (fun r hr => indexedMonomial_add_left a b r (Finset.mem_range.mp hr))
    · exact Finset.sum_congr rfl (fun r _ => indexedMonomial_add_right a b r)
  | mul a b ha hb =>
    rw [monomialCount, sum_range_blocks, toPolynomial, ← ha, ← hb, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [indexedMonomial_mul]
    have hdiv : (i * b.monomialCount + j) / b.monomialCount = i := by
      rw [Nat.mul_comm i b.monomialCount, Nat.add_comm (b.monomialCount * i) j,
        Nat.add_mul_div_left _ _ b.monomialCount_pos, Nat.div_eq_of_lt (Finset.mem_range.mp hj), Nat.zero_add]
    have hmod : (i * b.monomialCount + j) % b.monomialCount = j := by
      rw [Nat.mul_comm i b.monomialCount, Nat.add_comm (b.monomialCount * i) j,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    rw [hdiv, hmod]

end LeanCanny.ETR.Term
