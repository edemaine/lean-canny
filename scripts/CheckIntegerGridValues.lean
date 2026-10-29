import LeanCanny.Geometry.IntegerGridValueCertificate

/-! Explicit determinant certificates retain repeated grid roots.
Run with `lake env lean -DwarningAsError=true scripts/CheckIntegerGridValues.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open scoped Classical

namespace IntegerGridValueRegression
private noncomputable def p : Fin 1 → Polynomial (Polynomial ℤ) :=
  fun _ => (Polynomial.X * (Polynomial.X - 1)) ^ 2
private noncomputable def q : MvPolynomial (Fin 1) (Polynomial ℤ) := X 0

private lemma positive (i : Fin 1) : 0 < (p i).natDegree := by
  change 0 < ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial (Polynomial ℤ)) ^ 2).natDegree
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_mul Polynomial.X_ne_zero
    (Polynomial.X_sub_C_ne_zero 1), Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]
  decide


private lemma root_zero (rho : Polynomial ℤ →+* ℝ) (i : Fin 1) :
    (p i).eval₂ rho 0 = 0 := by
  change ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial (Polynomial ℤ)) ^ 2).eval₂ rho 0 = 0
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X]
  norm_num

private lemma root_one (rho : Polynomial ℤ →+* ℝ) (i : Fin 1) :
    (p i).eval₂ rho 1 = 0 := by
  change ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial (Polynomial ℤ)) ^ 2).eval₂ rho 1 = 0
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X]
  norm_num

-- The fixed integer determinant is nonzero without supplying a specialization.
example : IntegerGridValueCertificate.polynomial p q ≠ 0 :=
  IntegerGridValueCertificate.ne_zero p q positive

-- Both repeated roots, and their two different test values, are retained.
example (t : ℝ) :
    (IntegerGridValueCertificate.polynomial p q).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation t) 0 = 0 ∧
      (IntegerGridValueCertificate.polynomial p q).eval₂
        (SymbolicScaledSquarefree.scalarEvaluation t) 1 = 0 := by
  constructor
  · simpa [q] using IntegerGridValueCertificate.eval_eq_zero p q
      (SymbolicScaledSquarefree.scalarEvaluation t) (fun _ => 0) (root_zero _)
  · simpa [q] using IntegerGridValueCertificate.eval_eq_zero p q
      (SymbolicScaledSquarefree.scalarEvaluation t) (fun _ => 1) (root_one _)

-- A zero test still has a nonzero annihilator and zero is retained.
example : IntegerGridValueCertificate.polynomial p 0 ≠ 0 ∧
    ∀ t : ℝ, (IntegerGridValueCertificate.polynomial p 0).eval₂
      (SymbolicScaledSquarefree.scalarEvaluation t) 0 = 0 := by
  refine ⟨IntegerGridValueCertificate.ne_zero p 0 positive, ?_⟩
  intro t
  simpa using IntegerGridValueCertificate.eval_eq_zero p 0
    (SymbolicScaledSquarefree.scalarEvaluation t) (fun _ => 0) (root_zero _)

-- No coordinates is a legitimate grid; every constant test is covered.
example (q : MvPolynomial (Fin 0) (Polynomial ℤ)) :
    IntegerGridValueCertificate.polynomial (fun i : Fin 0 => i.elim0) q ≠ 0 := by
  apply IntegerGridValueCertificate.ne_zero
  intro i
  exact i.elim0

example (p : Fin 0 → Polynomial (Polynomial ℤ)) (q : MvPolynomial (Fin 0) (Polynomial ℤ))
    (rho : Polynomial ℤ →+* ℝ) :
    (IntegerGridValueCertificate.polynomial p q).eval₂ rho (q.eval₂ rho (fun i => i.elim0)) = 0 := by
  apply IntegerGridValueCertificate.eval_eq_zero
  intro i
  exact i.elim0

end IntegerGridValueRegression
