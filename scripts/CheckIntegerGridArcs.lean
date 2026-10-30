import LeanCanny.Connectivity.IntegerGridArcs
import LeanCanny.Geometry.PolynomialCoordinateProper

/-! Explicit exceptional factors control repeated grid branches.
Run with `lake env lean -DwarningAsError=true scripts/CheckIntegerGridArcs.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity Polynomial Set
open scoped Classical BigOperators

namespace ExplicitGridArcRegression
private noncomputable def p : Fin 1 → Polynomial (Polynomial ℤ) :=
  fun _ => (Polynomial.X * (Polynomial.X - Polynomial.C 1)) ^ 2
private noncomputable def q : Fin 1 → MvPolynomial (Fin 1) (Polynomial ℤ) :=
  fun _ => MvPolynomial.X 0

private lemma monic (i : Fin 1) : (p i).Monic :=
  (Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1)).pow 2

private lemma positive (i : Fin 1) : 0 < (p i).natDegree := by
  change 0 < ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial (Polynomial ℤ)) ^ 2).natDegree
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_mul Polynomial.X_ne_zero
    (Polynomial.X_sub_C_ne_zero 1), Polynomial.natDegree_X, Polynomial.natDegree_X_sub_C]
  decide

private lemma constant_coordinate (i : Fin 1) (k : ℕ) : ((p i).coeff k).natDegree ≤ 0 := by
  have h : p i = ((Polynomial.X * (Polynomial.X - Polynomial.C 1) : Polynomial ℤ) ^ 2).map Polynomial.C := by
    simp [p]
  rw [h, Polynomial.coeff_map]
  simp

private lemma constant_test (k : Fin 1) (u : Fin 1 →₀ ℕ) : ((q k).coeff u).natDegree ≤ 0 := by
  simp only [q, MvPolynomial.coeff_X]
  split_ifs <;> simp

-- A constant family produces a constant nonzero exceptional polynomial.
private lemma degree_zero : (IntegerGridArcs.exceptional p q).natDegree = 0 := by
  have h := IntegerGridArcs.exceptional_degree_le p q 0 constant_coordinate constant_test
  simpa using h

private lemma avoid (t : ℝ) : SymbolicScaledSquarefree.scalarEvaluation t
    (IntegerGridArcs.exceptional p q) ≠ 0 := by
  have hn := IntegerGridArcs.exceptional_ne_zero p q positive
  have he := Polynomial.eq_C_of_natDegree_eq_zero degree_zero
  rw [he] at hn ⊢
  simpa [SymbolicScaledSquarefree.scalarEvaluation] using
    (Int.cast_ne_zero.mpr (Polynomial.C_ne_zero.mp hn) :
      ((IntegerGridArcs.exceptional p q).coeff 0 : ℝ) ≠ 0)

private lemma original_zero (t : ℝ) (x : Fin 1 → ℝ) :
    PolynomialGridValues.value (IntegerGridArcs.realRows q) (t, x) = 0 ↔ x 0 = 0 := by
  simp only [funext_iff, Pi.zero_apply, IntegerGridArcs.real_value, q, MvPolynomial.eval₂_X]
  simp

-- The explicit factor excludes no parameter for this constant grid.
-- The repeated root at one is rejected, and the zero branch retains both endpoints.
example (a b : ℝ) (t₀ : Ioo a b) :
    ∃ curve : PolynomialGridArcs.Fiber (IntegerGridArcs.realRows q) t₀.val → ℝ → Fin 1 → ℝ,
      (∀ j t, t ∈ Icc a b → curve j t 0 = 0) ∧
      ∀ t : Ioo a b, ∀ x, x 0 = 0 ↔ ∃! j, curve j t.val = x := by
  have hproper : IsProperMap (RootProjection.projection (SquarefreeRootFamily.value p)) := by
    apply PolynomialCoordinateProper.proper_of_monic
    intro i
    exact (monic i).map _
  have hcapture (t : ℝ) (x : Fin 1 → ℝ)
      (hx : PolynomialGridValues.value (IntegerGridArcs.realRows q) (t, x) = 0) :
      SquarefreeRootFamily.value p (t, x) = 0 := by
    have hx0 := (original_zero t x).mp hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp only [SquarefreeRootFamily.value_apply, p, Polynomial.eval₂_pow, Polynomial.eval₂_mul,
      Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, hi, hx0, zero_mul,
      zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]
  obtain ⟨_, curve, _, _, hroot, hcomplete, _⟩ := IntegerGridArcs.anchored_arcs p q positive
    hproper hcapture a b t₀ (fun t _ => avoid t)
  exact ⟨curve, fun j t ht => (original_zero t _).mp (hroot j t ht),
    fun t x => (original_zero t.val x).symm.trans (hcomplete t x)⟩

-- No tests means no filtering factors. A zero test still has a nonzero factor.
example : IntegerGridArcs.exceptional p (fun i : Fin 0 => i.elim0) =
    ∏ i, SymbolicScaledSquarefree.exceptional (p i) := by
  simp [IntegerGridArcs.exceptional]

example : IntegerGridArcs.exceptional p (fun _ : Fin 1 => 0) ≠ 0 :=
  IntegerGridArcs.exceptional_ne_zero p _ positive

-- No coordinates and no tests yield the unit exceptional factor.
example : IntegerGridArcs.exceptional (fun i : Fin 0 => i.elim0)
    (fun i : Fin 0 => i.elim0) = 1 := by
  simp [IntegerGridArcs.exceptional]

end ExplicitGridArcRegression
