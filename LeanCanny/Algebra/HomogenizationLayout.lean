/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.WeightedHomogenization
public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Fixed-width layout for homogenization of a point-variable prefix

The new homogenizing coordinate occupies block zero. All original coordinates
move right by one block, with their order unchanged. Coefficient parameters have
weight zero and retain their original exponents.
-/

@[expose] public section

namespace LeanCanny.Algebra.HomogenizationLayout
open LeanCanny.Encoding
open FixedWidthPolynomial WeightedHomogenization
open scoped BigOperators

variable {σ : Type*} [Fintype σ] {N : ℕ}

def prefixWeight (f : σ ≃ Fin N) (A : ℕ) (i : σ) : ℕ := if (f i).val < A then 1 else 0

omit [Fintype σ] in
/-- Selecting the whole variable layout gives ordinary total-degree homogenization. -/
@[simp] theorem prefixWeight_all (f : σ ≃ Fin N) : prefixWeight f N = fun _ => 1 := by
  funext i
  simp only [prefixWeight, (f i).isLt, ite_true]

def variableEquiv (f : σ ≃ Fin N) : Option σ ≃ Fin (N + 1) :=
  (Equiv.optionCongr f).trans (finSuccEquiv N).symm

omit [Fintype σ] in
@[simp] theorem variableEquiv_none (f : σ ≃ Fin N) : (variableEquiv f none).val = 0 := by
  simp [variableEquiv]

omit [Fintype σ] in
@[simp] theorem variableEquiv_some (f : σ ≃ Fin N) (i : σ) : (variableEquiv f (some i)).val = (f i).val + 1 := by
  simp [variableEquiv]

omit [Fintype σ] in
theorem weights_prefix (f : σ ≃ Fin N) (A : ℕ) :
    weights (prefixWeight f A) = prefixWeight (variableEquiv f) (A + 1) := by
  funext i
  cases i with
  | none => simp [weights, prefixWeight]
  | some i => simp [weights, prefixWeight]

omit [Fintype σ] in
theorem prefixWeight_le_one (f : σ ≃ Fin N) (A : ℕ) (i : σ) : prefixWeight f A i ≤ 1 := by
  unfold prefixWeight
  split_ifs <;> decide

theorem weight_native (f : σ ≃ Fin N) (A W r : ℕ) :
    Finsupp.weight (prefixWeight f A) (nativeExponent f W r) =
      ∑ i : Fin N, if i.val < A then entry W r i.val else 0 := by
  rw [Finsupp.weight_eq_sum]
  calc
    _ = ∑ i : σ, if (f i).val < A then entry W r (f i).val else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [prefixWeight, nativeExponent, smul_eq_mul]
    _ = _ := Equiv.sum_comp f (fun i : Fin N => if i.val < A then entry W r i.val else 0)

theorem entry_drop (W r i : ℕ) :
    entry W (Nat.fromBitsLE (r.bits.drop W)) i = entry W r (i + 1) := by
  rw [entry_eq_digit, drop_value, Nat.fromBitsLE_bits, Nat.div_div_eq_div_mul,
    ← pow_add, entry_eq_digit]
  have he : W + i * W = (i + 1) * W := by rw [Nat.add_mul, Nat.one_mul]; omega
  rw [he]

theorem native_some (f : σ ≃ Fin N) (W r : ℕ) :
    (nativeExponent (variableEquiv f) W r).some = nativeExponent f W (Nat.fromBitsLE (r.bits.drop W)) := by
  ext i
  simp only [Finsupp.some_apply, nativeExponent, Finsupp.coe_equivFunOnFinite_symm, variableEquiv_some]
  exact (entry_drop W r (f i).val).symm

def weightedSum (N A W r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (N + 1), if i < A + 1 then entry W r i else 0

theorem weight_new_native (f : σ ≃ Fin N) (A W r : ℕ) :
    Finsupp.weight (weights (prefixWeight f A)) (nativeExponent (variableEquiv f) W r) = weightedSum N A W r := by
  rw [weights_prefix, weight_native, weightedSum, Finset.sum_range]

theorem coefficient_rank {R : Type*} [CommSemiring R] (f : σ ≃ Fin N) (A D W r : ℕ)
    (p : MvPolynomial σ R) :
    (homogenize (prefixWeight f A) D p).coeff (nativeExponent (variableEquiv f) W r) =
      if weightedSum N A W r = D then p.coeff (nativeExponent f W (Nat.fromBitsLE (r.bits.drop W))) else 0 := by
  rw [coefficient, weight_new_native, native_some]

theorem eval_chart {R S : Type*} [CommSemiring R] [CommSemiring S] (f : σ ≃ Fin N)
    (A D : ℕ) (p : MvPolynomial σ R) (hp : p.totalDegree ≤ D) (φ : R →+* S) (x : σ → S) :
    (homogenize (prefixWeight f A) D p).eval₂ φ (fun i => i.elim 1 x) = p.eval₂ φ x := by
  apply WeightedHomogenization.eval_chart
  intro e he
  exact (weight_le_degree _ (prefixWeight_le_one f A) e).trans ((MvPolynomial.le_totalDegree he).trans hp)

end LeanCanny.Algebra.HomogenizationLayout
