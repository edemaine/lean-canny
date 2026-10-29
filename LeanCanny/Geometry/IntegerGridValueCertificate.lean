/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateInfinity
public import LeanCanny.Algebra.AffineRingGramBounds
public import LeanCanny.Algebra.ProjectiveValueGram
public import LeanCanny.Geometry.UnivariateRootFamily
public import LeanCanny.Algebra.SymbolicScaledSquarefreeSmall

/-! # Explicit polynomial-value certificates on integer coordinate grids

The fixed reciprocal Gram determinant constructs one integer parameter
polynomial annihilating a test on every grid root, at every specialization.
A real specialization with nonzero leading coefficients proves nonvanishing.
No irreducible factorization or regularity of the grid roots is used.
-/

@[expose] public section
namespace LeanCanny.Geometry.IntegerGridValueCertificate
open LeanCanny.Algebra MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
abbrev Base := Polynomial ℤ

noncomputable def rows (p : Fin n → Polynomial Base) (i : Fin n) : MvPolynomial (Fin n) Base :=
  (p i).toMvPolynomial i

noncomputable def degrees (p : Fin n → Polynomial Base) (i : Fin n) : ℕ := (p i).natDegree

noncomputable def testDegree (q : MvPolynomial (Fin n) Base) : ℕ := q.totalDegree + 1

noncomputable def test (q : MvPolynomial (Fin n) Base) : MvPolynomial (Fin (n + 1)) Base :=
  rename (AffineFiniteCoordinates.layout n) (homogenize (fun _ => 1) (testDegree q) q)

noncomputable def width (p : Fin n → Polynomial Base) (q : MvPolynomial (Fin n) Base) : ℕ :=
  (Macaulay.level (ProjectiveValueGram.degrees (degrees p) (testDegree q))).size

noncomputable def polynomial (p : Fin n → Polynomial Base) (q : MvPolynomial (Fin n) Base) :
    Polynomial Base :=
  ProjectiveValueGram.annihilator (AffineRingCoordinates.homogeneousRows (rows p) (degrees p))
    (test q) (degrees p) (testDegree q) (width p q)

lemma test_homogeneous (q : MvPolynomial (Fin n) Base) : (test q).IsHomogeneous (testDegree q) := by
  have hw : weights (fun _ : Fin n => 1) = 1 := by funext j; cases j <;> rfl
  apply IsHomogeneous.rename_isHomogeneous
  simpa only [IsHomogeneous, hw] using WeightedHomogenization.homogeneous
    (fun _ : Fin n => 1) (testDegree q) q

lemma test_eval {K : Type*} [Field K] (q : MvPolynomial (Fin n) Base)
    (rho : Base →+* K) (x : Fin n → K) :
    (test q).eval₂ rho (AffineFiniteCoordinates.point x) = q.eval₂ rho x := by
  rw [test, eval₂_rename]
  have he : AffineFiniteCoordinates.point x ∘ AffineFiniteCoordinates.layout n =
      fun j => j.elim 1 x := by
    funext j
    simp [AffineFiniteCoordinates.point]
  rw [he]
  apply WeightedHomogenization.eval_chart
  intro e he
  exact (weight_le_degree _ (by simp) e).trans ((le_totalDegree he).trans (Nat.le_succ _))

lemma eval_eq_zero {K : Type*} [Field K] (p : Fin n → Polynomial Base)
    (q : MvPolynomial (Fin n) Base) (rho : Base →+* K) (x : Fin n → K)
    (hx : ∀ i, (p i).eval₂ rho (x i) = 0) :
    (polynomial p q).eval₂ rho (q.eval₂ rho x) = 0 := by
  have h := ProjectiveValueGram.annihilator_eval
    (AffineRingCoordinates.homogeneousRows (rows p) (degrees p)) (test q) (degrees p)
    (testDegree q) (width p q) (Nat.lt_size_self _) (AffineRingCoordinates.homogeneous _ _)
    (test_homogeneous q) rho (AffineFiniteCoordinates.point x) (AffineFiniteCoordinates.point_zero x) (by
      intro i
      rw [AffineRingCoordinates.eval_rows rho (rows p) (degrees p)
        (fun i => UnivariateInfinity.degree_le (p i) i)]
      exact (UnivariateRootFamily.eval _ _ _ _).trans (hx i))
  rwa [test_eval] at h

lemma ne_zero_of_leading (p : Fin n → Polynomial Base) (q : MvPolynomial (Fin n) Base)
    (hp : ∀ i, 0 < (p i).natDegree) (rho : Base →+* ℝ)
    (hl : ∀ i, (Complex.ofRealHom.comp rho) (p i).leadingCoeff ≠ 0) : polynomial p q ≠ 0 := by
  exact ProjectiveValueGram.annihilator_ne_zero
    (AffineRingCoordinates.homogeneousRows (rows p) (degrees p)) (test q) (degrees p)
    (testDegree q) (width p q) (Nat.lt_size_self _) (AffineRingCoordinates.homogeneous _ _)
    (test_homogeneous q) hp (Nat.zero_lt_succ _) rho
    (AffineRingCoordinates.noInfinity_layout _ _ _ (UnivariateInfinity.noInfinity p hp _ hl))

lemma degree_le (p : Fin n → Polynomial Base) (q : MvPolynomial (Fin n) Base) :
    (polynomial p q).natDegree ≤ ProjectiveValueGram.dimension n (width p q) + 1 :=
  ProjectiveValueGram.annihilator_degree_le _ _ _ _ _

lemma exists_leading_specialization (p : Fin n → Polynomial Base) (hp : ∀ i, p i ≠ 0) :
    ∃ t : ℝ, ∀ i, SymbolicScaledSquarefree.scalarEvaluation t (p i).leadingCoeff ≠ 0 := by
  let lead (i : Fin n) := (p i).leadingCoeff.map (Int.castRingHom ℝ)
  have hn (i : Fin n) : lead i ≠ 0 := (Polynomial.map_ne_zero_iff
    (Int.cast_injective (α := ℝ))).mpr (Polynomial.leadingCoeff_ne_zero.mpr (hp i))
  have hf : (⋃ i, {t : ℝ | Polynomial.IsRoot (lead i) t}).Finite :=
    Set.finite_iUnion (fun i => Polynomial.finite_setOfPred_isRoot (hn i))
  obtain ⟨t, ht⟩ := hf.exists_notMem
  refine ⟨t, ?_⟩
  intro i hi
  apply ht
  apply Set.mem_iUnion.mpr
  refine ⟨i, ?_⟩
  simpa only [Set.mem_ofPred_eq, lead, Polynomial.IsRoot, Polynomial.eval_map,
    SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom] using hi

lemma ne_zero (p : Fin n → Polynomial Base) (q : MvPolynomial (Fin n) Base)
    (hp : ∀ i, 0 < (p i).natDegree) : polynomial p q ≠ 0 := by
  have hn (i : Fin n) : p i ≠ 0 := by
    intro hz
    have h := hp i
    rw [hz, Polynomial.natDegree_zero] at h
    exact (Nat.lt_irrefl 0) h
  obtain ⟨t, ht⟩ := exists_leading_specialization p hn
  apply ne_zero_of_leading p q hp (SymbolicScaledSquarefree.scalarEvaluation t)
  intro i hi
  exact ht i (Complex.ofReal_injective hi)

lemma row_coefficient_inner_degree (p : Fin n → Polynomial Base) (E : ℕ)
    (hp : ∀ i k, ((p i).coeff k).natDegree ≤ E) (i : Fin n) (u : Fin n →₀ ℕ) :
    ((rows p i).coeff u).natDegree ≤ E := by
  conv_lhs => rw [rows, ← Polynomial.sum_monomial_eq (p i), Polynomial.sum_def, map_sum, coeff_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  rw [UnivariateInfinity.monomial, coeff_monomial]
  split_ifs
  · exact hp i k
  · simp

lemma test_coefficient_inner_degree (q : MvPolynomial (Fin n) Base) (E : ℕ)
    (hq : ∀ u, (q.coeff u).natDegree ≤ E) (u : Fin (n + 1) →₀ ℕ) :
    ((test q).coeff u).natDegree ≤ E := by
  by_cases hz : (test q).coeff u = 0
  · simp [hz]
  · obtain ⟨v, hv, _⟩ := coeff_rename_ne_zero (AffineFiniteCoordinates.layout n) _ u hz
    rw [test, ← hv, coeff_rename_mapDomain _ (AffineFiniteCoordinates.layout n).injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hq _
    · simp

lemma parameter_degree_le (p : Fin n → Polynomial Base) (q : MvPolynomial (Fin n) Base)
    (E : ℕ) (hp : ∀ i k, ((p i).coeff k).natDegree ≤ E)
    (hq : ∀ u, (q.coeff u).natDegree ≤ E) (k : ℕ) :
    ((polynomial p q).coeff k).natDegree ≤ ProjectiveValueGram.dimension n (width p q) * E :=
  ProjectiveValueGram.annihilator_inner_degree _ _ _ _ _ E
    (AffineRingCoordinates.homogeneous_coefficient_inner_degree (rows p) (degrees p) E
      (row_coefficient_inner_degree p E hp)) (test_coefficient_inner_degree q E hq) k

end LeanCanny.Geometry.IntegerGridValueCertificate
