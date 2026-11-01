/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.ClosedFormulaSingleEquation
public import LeanCanny.Computation.PolyTimeBinaryNat
/-! # The single algebraic equation has one degree budget from the original formula -/
@[expose] public section
namespace LeanCanny.Connectivity.ClosedFormulaWitness
open ETR MvPolynomial LeanCanny.Computation
open scoped Classical

private theorem double_budget {a s t B : ℕ} (H : a≤2^s*B) (HS : s+1≤t) : 2*a≤2^t*B := by
  calc
    2*a ≤ 2*(2^s*B) := Nat.mul_le_mul_left 2 H
    _ = 2^(s+1)*B := by rw [pow_succ]; ring
    _ ≤ 2^t*B := Nat.mul_le_mul_right B (Nat.pow_le_pow_right (by decide) HS)

private theorem atomPolynomial_degree {p : Formula} (hp : Closed p) (n : ℕ) (q : Formula) :
    (atomPolynomial n p q).totalDegree ≤ max (2*p.toData.size) 2 := by
  unfold atomPolynomial
  split
  · exact polynomial_original_degree hp n _
  · simp only [MvPolynomial.totalDegree_C]
    exact Nat.zero_le _

theorem aggregate_degree {p : Formula} (hp : Closed p) (n : ℕ) {q : Formula} (hq : Closed q) :
    (aggregate n p q).totalDegree ≤ 2^q.toData.size * max (2*p.toData.size) 2 := by
  induction hq with
  | falsum => simp [aggregate]
  | verum => simp [aggregate]
  | eqZero t =>
    exact (atomPolynomial_degree hp n _).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  | nonnegative t =>
    exact (atomPolynomial_degree hp n _).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  | @and a b _ _ HA HB =>
    have HSA : a.toData.size+1 ≤ (Formula.and a b).toData.size := by
      simp only [Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
      omega
    have HSB : b.toData.size+1 ≤ (Formula.and a b).toData.size := by
      simp only [Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
      omega
    exact (MvPolynomial.totalDegree_add _ _).trans
      (max_le ((MvPolynomial.totalDegree_pow _ 2).trans (double_budget HA HSA))
        ((MvPolynomial.totalDegree_pow _ 2).trans (double_budget HB HSB)))
  | @or a b _ _ HA HB =>
    have HSA : a.toData.size+1 ≤ (Formula.or a b).toData.size := by
      simp only [Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
      omega
    have HSB : b.toData.size+1 ≤ (Formula.or a b).toData.size := by
      simp only [Formula.toData,LeanCanny.Data.cons_size,LeanCanny.Data.size_empty,Codec.unary_size]
      omega
    have HDa := double_budget HA HSA
    have HDb := double_budget HB HSB
    apply (MvPolynomial.totalDegree_mul _ _).trans
    omega

def equationDegreeBudget (p : Formula) : ℕ := 2^p.toData.size * max (2*p.toData.size) 2

theorem equation_degree {p : Formula} (hp : Closed p) (n : ℕ) :
    (aggregate n p p).totalDegree ≤ equationDegreeBudget p := aggregate_degree hp n hp

theorem equationDegreeBudget_binary {p : List Bool → Formula} (hp : (fun q => (p q).encode) ∈ LeanCanny.FP) :
    LeanCanny.BinaryFn (fun q => equationDegreeBudget (p q)) := by
  have HS : LeanCanny.UnaryFn (fun q => (p q).toData.size) :=
    (LeanCanny.UnaryFn.length hp).of_eq (fun _ => LeanCanny.Data.length_toBits _)
  exact ((LeanCanny.BinaryFn.const 2).powUnary HS).mul
    (LeanCanny.BinaryFn.ofUnary (((LeanCanny.UnaryFn.const 2).mul HS).max (LeanCanny.UnaryFn.const 2)))

end LeanCanny.Connectivity.ClosedFormulaWitness
