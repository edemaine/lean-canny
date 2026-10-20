/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.EquationDegree
public import LeanCanny.Geometry.CubePolynomial

/-! # Finite-variable polynomials and compact zero sets for ETR terms

Unused variables are replaced by zero. At the term's arity this preserves
existential real-zero semantics. The rational cube change then gives a bounded
integer polynomial and compact zero sets with positive boundary margins.
-/

@[expose] public section

namespace LeanCanny.ETR.Term

noncomputable def finitePolynomial (n : ℕ) : Term → MvPolynomial (Fin n) ℤ
  | .const z => MvPolynomial.C z
  | .var i => if h : i < n then MvPolynomial.X ⟨i, h⟩ else 0
  | .add t u => finitePolynomial n t + finitePolynomial n u
  | .mul t u => finitePolynomial n t * finitePolynomial n u

theorem eval_finitePolynomial (t : Term) (n : ℕ) (y : Fin n → ℝ) :
    (finitePolynomial n t).eval₂ (Int.castRingHom ℝ) y = t.eval (Formula.extend y) := by
  induction t with
  | const z => simp only [finitePolynomial, MvPolynomial.eval₂_C, Int.coe_castRingHom, eval]
  | var i =>
    by_cases hi : i < n
    · simp only [finitePolynomial, hi, ↓reduceDIte, MvPolynomial.eval₂_X, eval, Formula.extend]
    · simp only [finitePolynomial, hi, ↓reduceDIte, MvPolynomial.eval₂_zero, eval, Formula.extend]
  | add t u ht hu => simp only [finitePolynomial, MvPolynomial.eval₂_add, ht, hu, eval]
  | mul t u ht hu => simp only [finitePolynomial, MvPolynomial.eval₂_mul, ht, hu, eval]

theorem totalDegree_finitePolynomial (t : Term) (n : ℕ) : (finitePolynomial n t).totalDegree ≤ t.degreeBound := by
  induction t with
  | const z => simp only [finitePolynomial, degreeBound, MvPolynomial.totalDegree_C, Nat.le_refl]
  | var i =>
    simp only [finitePolynomial, degreeBound]
    split_ifs <;> simp
  | add t u ht hu => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max ht hu)
  | mul t u ht hu => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add ht hu)

theorem exists_zero_iff_finitePolynomial (t : Term) :
    (∃ env : ℕ → ℝ, t.eval env = 0) ↔
      ∃ y : Fin t.arity → ℝ, (finitePolynomial t.arity t).eval₂ (Int.castRingHom ℝ) y = 0 := by
  have h := Formula.satisfiable_iff_fin (.eqZero t)
  simpa only [Formula.Satisfiable, Formula.Holds, Formula.arity, eval_finitePolynomial] using h

noncomputable def compactPolynomial (t : Term) : MvPolynomial (Fin t.arity) ℤ :=
  Geometry.CubePolynomial.cleared (finitePolynomial t.arity t)

def compactZeroSet (t : Term) (epsilon : ℝ) : Set (Fin t.arity → ℝ) :=
  Geometry.CubePolynomial.zeroSet (finitePolynomial t.arity t) epsilon

theorem isCompact_compactZeroSet (t : Term) (epsilon : ℝ) : IsCompact (compactZeroSet t epsilon) :=
  Geometry.CubePolynomial.isCompact_zeroSet _ _

theorem exists_zero_iff_compact (t : Term) :
    (∃ env : ℕ → ℝ, t.eval env = 0) ↔ ∃ epsilon : ℝ, 0 < epsilon ∧ (compactZeroSet t epsilon).Nonempty :=
  t.exists_zero_iff_finitePolynomial.trans (Geometry.CubePolynomial.exists_zero_iff_nonempty _)

theorem compactZeroSet_mono (t : Term) {epsilon eta : ℝ} (h : eta ≤ epsilon) :
    compactZeroSet t epsilon ⊆ compactZeroSet t eta := Geometry.CubePolynomial.zeroSet_mono _ h

theorem compactPolynomial_degree (t : Term) : t.compactPolynomial.totalDegree ≤ 4 * t.arity * t.degreeBound :=
  (Geometry.CubePolynomial.totalDegree_le_card _).trans (by
    rw [Fintype.card_fin]
    exact Nat.mul_le_mul_left _ (totalDegree_finitePolynomial t t.arity))

theorem compactPolynomial_degree_size (t : Term) : t.compactPolynomial.totalDegree ≤ 4 * t.toData.size ^ 2 := by
  apply t.compactPolynomial_degree.trans
  rw [pow_two, ← Nat.mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 t.arity_le_dataSize) t.degreeBound_le_dataSize

end LeanCanny.ETR.Term
