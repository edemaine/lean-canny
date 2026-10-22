/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Data.Nat.Size

/-!
# Integer coefficient bounds for polynomial determinants

The sum of the absolute values of a polynomial's coefficients bounds every
coefficient. Multiplying by another polynomial increases a uniform coefficient
bound by at most that sum. Applying this successively to the Leibniz expansion
gives a determinant bound with a separate allowance for each column.

These are size estimates, not an algorithm for evaluating determinants.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

theorem det_natDegree_le {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial R)) (D : ι → ℕ)
    (hD : ∀ i j, (A i j).natDegree ≤ D j) :
    A.det.natDegree ≤ ∑ j, D j := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => hD (σ j) j))

theorem resultant_natDegree_le {R : Type*} [CommRing R]
    (f g : Polynomial (Polynomial R)) (m n Df Dg : ℕ)
    (hf : ∀ i, (f.coeff i).natDegree ≤ Df)
    (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (f.resultant g m n).natDegree ≤ m * Dg + n * Df := by
  classical
  have hcol : ∀ i j : Fin (m + n),
      (Polynomial.sylvester f g m n i j).natDegree ≤
        j.addCases (fun _ => Dg) (fun _ => Df) := by
    intro i j
    induction j using Fin.addCases <;> simp only [Polynomial.sylvester, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · exact hg _
      · simp
    · split_ifs
      · exact hf _
      · simp
  have h := det_natDegree_le (Polynomial.sylvester f g m n)
    (fun j => j.addCases (fun _ => Dg) (fun _ => Df)) hcol
  simpa only [Polynomial.resultant, Fin.sum_univ_add, Fin.addCases_left,
    Fin.addCases_right, Fin.sum_const, smul_eq_mul] using h

/-- The sum of the absolute values of the integer coefficients. -/
noncomputable def coefficientMass (p : Polynomial ℤ) : ℕ :=
  p.sum fun _ a => a.natAbs

@[simp] theorem coefficientMass_zero : coefficientMass 0 = 0 := by
  simp [coefficientMass]

@[simp] theorem coefficientMass_C (a : ℤ) : coefficientMass (C a) = a.natAbs := by
  rw [coefficientMass, Polynomial.sum_C_index]
  rfl

theorem coefficientMass_le (p : Polynomial ℤ) (d H : ℕ)
    (hd : p.natDegree ≤ d) (hH : ∀ k, (p.coeff k).natAbs ≤ H) :
    coefficientMass p ≤ (d + 1) * H := by
  rw [coefficientMass, p.sum_over_range' (fun _ => rfl) (d + 1) (by omega)]
  calc
    _ ≤ ∑ _ ∈ Finset.range (d + 1), H := Finset.sum_le_sum fun k _ => hH k
    _ = _ := by simp

/-- A coefficient bound for one factor needs only the coefficient mass of the
other factor; its degree need not be retained in the intermediate state. -/
theorem coeff_natAbs_mul_le (p q : Polynomial ℤ) (A k : ℕ)
    (hp : ∀ i, (p.coeff i).natAbs ≤ A) :
    ((p * q).coeff k).natAbs ≤ A * coefficientMass q := by
  classical
  have hsum : p * q = ∑ j ∈ q.support, (p * C (q.coeff j)) * X ^ j := by
    conv_lhs => rw [q.as_sum_support_C_mul_X_pow]
    simp only [Finset.mul_sum, mul_assoc]
  rw [hsum, Polynomial.finsetSum_coeff]
  calc
    _ ≤ ∑ j ∈ q.support, (((p * C (q.coeff j)) * X ^ j).coeff k).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ j ∈ q.support, A * (q.coeff j).natAbs := by
      apply Finset.sum_le_sum
      intro j _
      rw [Polynomial.coeff_mul_X_pow']
      split_ifs
      · rw [Polynomial.coeff_mul_C, Int.natAbs_mul]
        exact Nat.mul_le_mul_right _ (hp _)
      · exact Nat.zero_le _
    _ = A * coefficientMass q := by
      simp only [coefficientMass, Polynomial.sum, Finset.mul_sum]

theorem coeff_natAbs_le_coefficientMass (p : Polynomial ℤ) (k : ℕ) :
    (p.coeff k).natAbs ≤ coefficientMass p := by
  have h := coeff_natAbs_mul_le 1 p 1 k (by
    intro i
    simp only [Polynomial.coeff_one]
    split_ifs <;> decide)
  simpa only [one_mul] using h

theorem coeff_natAbs_prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℤ)
    (B : ι → ℕ) (hB : ∀ i ∈ s, coefficientMass (f i) ≤ B i) (k : ℕ) :
    ((∏ i ∈ s, f i).coeff k).natAbs ≤ ∏ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty => simp only [Finset.prod_empty, Polynomial.coeff_one]; split_ifs <;> decide
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_comm (f i)]
      exact (coeff_natAbs_mul_le _ _ _ k
        (fun j => ih (fun a ha => hB a (Finset.mem_insert_of_mem ha)) j)).trans
          (by
            rw [Nat.mul_comm (B i)]
            exact Nat.mul_le_mul_left _ (hB i (Finset.mem_insert_self _ _)))

/-- A separate coefficient-mass allowance for each column also bounds any
polynomial submatrix whose entries satisfy the same allowances. -/
theorem det_coeff_natAbs_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial ℤ)) (B : ι → ℕ)
    (hB : ∀ i j, coefficientMass (A i j) ≤ B j) (k : ℕ) :
    (A.det.coeff k).natAbs ≤ (Fintype.card ι).factorial * ∏ j, B j := by
  classical
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι,
        ((Equiv.Perm.sign σ • ∏ j, A (σ j) j).coeff k).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ j, B j := by
      apply Finset.sum_le_sum
      intro σ _
      simp only [Polynomial.coeff_smul, Units.smul_def, smul_eq_mul, Int.natAbs_mul,
        Int.units_natAbs, one_mul]
      exact coeff_natAbs_prod_le _ _ B (fun j _ => hB (σ j) j) k
    _ = _ := by simp [Fintype.card_perm]

/-- Binary coefficient lengths depend on the sum of the column budgets, rather
than on the magnitude of their product. The estimate includes the empty matrix. -/
theorem det_coeff_size_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι (Polynomial ℤ)) (b : ι → ℕ)
    (hb : ∀ i j, coefficientMass (A i j) ≤ 2 ^ b j) (k : ℕ) :
    (A.det.coeff k).natAbs.size ≤
      (Fintype.card ι).size * Fintype.card ι + (∑ j, b j) + 1 := by
  classical
  have hfactorial : (Fintype.card ι).factorial ≤
      2 ^ ((Fintype.card ι).size * Fintype.card ι) := by
    calc
      _ ≤ Fintype.card ι ^ Fintype.card ι := Nat.factorial_le_pow _
      _ ≤ (2 ^ (Fintype.card ι).size) ^ Fintype.card ι :=
        Nat.pow_le_pow_left (Nat.lt_size_self _).le _
      _ = _ := (pow_mul _ _ _).symm
  have h := det_coeff_natAbs_le A (fun j => 2 ^ b j) hb k
  have hbound : (A.det.coeff k).natAbs ≤
      2 ^ ((Fintype.card ι).size * Fintype.card ι + ∑ j, b j) := by
    calc
      _ ≤ (Fintype.card ι).factorial * ∏ j, 2 ^ b j := h
      _ ≤ 2 ^ ((Fintype.card ι).size * Fintype.card ι) * ∏ j, 2 ^ b j :=
        Nat.mul_le_mul_right _ hfactorial
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
  simpa only [Nat.size_pow] using Nat.size_le_size hbound

/-- The Sylvester matrix has `m` columns from `g` and `n` columns from `f`.
The bounds use the specified degrees even when specialization lowers a degree. -/
theorem resultant_coeff_natAbs_le (f g : Polynomial (Polynomial ℤ))
    (m n Bf Bg : ℕ)
    (hf : ∀ i, coefficientMass (f.coeff i) ≤ Bf)
    (hg : ∀ i, coefficientMass (g.coeff i) ≤ Bg) (k : ℕ) :
    ((f.resultant g m n).coeff k).natAbs ≤
      (m + n).factorial * (Bg ^ m * Bf ^ n) := by
  classical
  have hcol : ∀ i j : Fin (m + n),
      coefficientMass (Polynomial.sylvester f g m n i j) ≤
        j.addCases (fun _ => Bg) (fun _ => Bf) := by
    intro i j
    induction j using Fin.addCases <;> simp only [Polynomial.sylvester, Matrix.of_apply,
      Fin.addCases_left, Fin.addCases_right]
    · split_ifs
      · exact hg _
      · simp
    · split_ifs
      · exact hf _
      · simp
  have h := det_coeff_natAbs_le (Polynomial.sylvester f g m n)
    (fun j => j.addCases (fun _ => Bg) (fun _ => Bf)) hcol k
  simpa only [Polynomial.resultant, Fintype.card_fin, Fin.prod_univ_add,
    Fin.addCases_left, Fin.addCases_right, Fin.prod_const] using h

theorem resultant_coeff_size_le (f g : Polynomial (Polynomial ℤ))
    (m n bf bg : ℕ)
    (hf : ∀ i, coefficientMass (f.coeff i) ≤ 2 ^ bf)
    (hg : ∀ i, coefficientMass (g.coeff i) ≤ 2 ^ bg) (k : ℕ) :
    ((f.resultant g m n).coeff k).natAbs.size ≤
      (m + n).size * (m + n) + m * bg + n * bf + 1 := by
  have h := resultant_coeff_natAbs_le f g m n (2 ^ bf) (2 ^ bg) hf hg k
  have hfactorial : (m + n).factorial ≤ 2 ^ ((m + n).size * (m + n)) :=
    (Nat.factorial_le_pow _).trans
      ((Nat.pow_le_pow_left (Nat.lt_size_self _).le _).trans_eq (pow_mul _ _ _).symm)
  have hbound : ((f.resultant g m n).coeff k).natAbs ≤
      2 ^ ((m + n).size * (m + n) + m * bg + n * bf) := by
    calc
      _ ≤ (m + n).factorial * ((2 ^ bg) ^ m * (2 ^ bf) ^ n) := h
      _ ≤ 2 ^ ((m + n).size * (m + n)) * ((2 ^ bg) ^ m * (2 ^ bf) ^ n) :=
        Nat.mul_le_mul_right _ hfactorial
      _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
  simpa only [Nat.size_pow] using Nat.size_le_size hbound

end LeanCanny.Algebra
