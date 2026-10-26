/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullWriter

/-! # Geometry of the full writer's actual finite coordinate order

The swept coordinate occupies the last input wire. An explicit permutation
identifies this order with the geometric source, preserving regularity and
properness. The source and mark wire models are exact integer polynomials
in these finite coordinates.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullGeometry
open MvPolynomial Set LeanCanny.Geometry LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Algebra
open scoped Classical
open scoped BigOperators

def inputIndex (k : ℕ) : Fin (k + 1) → Fin (k + 1) := Fin.cases (Fin.last k) Fin.castSucc
def inverseIndex (k : ℕ) : Fin (k + 1) → Fin (k + 1) := Fin.lastCases 0 Fin.succ

theorem inverse_index (k : ℕ) (j : Fin (k + 1)) : inverseIndex k (inputIndex k j) = j := by
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [inputIndex, inverseIndex]
theorem index_inverse (k : ℕ) (j : Fin (k + 1)) : inputIndex k (inverseIndex k j) = j := by
  refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [inputIndex, inverseIndex]

def inputEquiv (k : ℕ) : Fin (k + 1) ≃ Fin (k + 1) where
  toFun := inputIndex k
  invFun := inverseIndex k
  left_inv := inverse_index k
  right_inv := index_inverse k

def coordinates (k : ℕ) : (Fin (k + 1) → ℝ) ≃ₜ (Fin (k + 1) → ℝ) where
  toFun x i := x (inputIndex k i)
  invFun x i := x (inverseIndex k i)
  left_inv x := by funext i; exact congrArg x (index_inverse k i)
  right_inv x := by funext i; exact congrArg x (inverse_index k i)
  continuous_toFun := continuous_pi (fun i => continuous_apply (inputIndex k i))
  continuous_invFun := continuous_pi (fun i => continuous_apply (inverseIndex k i))

theorem freeze_finite (k : ℕ) (p : MvPolynomial (Fin (k + 1)) ℤ) :
    CircuitFreeze.substitution k (rename Fin.val p) = rename Fin.val (rename (inputIndex k) p) := by
  apply Differential.eq_of_eval_complex
  intro x
  rw [CircuitFreeze.eval_substitution, eval₂_rename, eval₂_rename, eval₂_rename]
  apply congrArg (p.eval₂ (Int.castRingHom ℂ))
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp [inputIndex]

noncomputable def polynomial {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) : MvPolynomial (Fin (n + 4)) ℤ :=
  rename (inputIndex (n + 3)) (BoundedRegularSource.polynomial q D b R)
noncomputable def markPolynomial {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (R : ℕ) : MvPolynomial (Fin (n + 4)) ℤ :=
  rename (inputIndex (n + 3)) (BoundedRegularSource.markPolynomial q R)

theorem polynomial_eq {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    polynomial q D b R = FermatCriticalHomogenization.polynomial
      (rename (inputIndex (n + 3)) (IntegerRegularSource.lower (BoundedRegularSource.lower q D b R)
        (BoundedZeroSource.powerDegree D) (BoundedRegularSource.sourceMassExponent n D b R)))
      (IntegerRegularSource.leading (n + 3) 1 (BoundedZeroSource.powerDegree D) (BoundedRegularSource.sourceMassExponent n D b R))
      (BoundedZeroSource.powerDegree D) := by
  have he : (∑ i : Fin (n + 4), (X (inputIndex (n + 3) i) : MvPolynomial (Fin (n + 4)) ℤ) ^ BoundedZeroSource.powerDegree D) =
      ∑ i : Fin (n + 4), (X i : MvPolynomial (Fin (n + 4)) ℤ) ^ BoundedZeroSource.powerDegree D :=
    (inputEquiv (n + 3)).sum_comp (fun i => (X i : MvPolynomial (Fin (n + 4)) ℤ) ^ BoundedZeroSource.powerDegree D)
  simp only [polynomial, BoundedRegularSource.polynomial, FermatCriticalHomogenization.polynomial,
    map_add, map_mul, rename_C, map_sum, map_pow, rename_X, he]

theorem source_identity (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (BoundedFullWriter.start P c)
      (BoundedFullWriter.program P c) (BoundedFullWriter.output P c) = rename Fin.val
        (polynomial (BoundedFullWriter.original P c) (BoundedFullWriter.size P c) (BoundedFullWriter.size P c) (P.radius c)) :=
  (BoundedFullWriter.source_identity P c ht).trans (freeze_finite _ _)

theorem mark_identity (P : BoundedFullWriter.Readers) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    Differential.symbolicRun (fun i => (X i : MvPolynomial ℕ ℤ)) (BoundedFullWriter.start P c)
      (BoundedFullWriter.program P c) (BoundedFullWriter.markOutput P c) = rename Fin.val
        (markPolynomial (BoundedFullWriter.original P c) (P.radius c)) :=
  (BoundedFullWriter.mark_identity P c ht).trans (freeze_finite _ _)

theorem proper {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    IsProperMap (fun x : Fin (n + 4) → ℝ => (polynomial q D b R).eval₂ (Int.castRingHom ℝ) x) := by
  have he : (fun x : Fin (n + 4) → ℝ => (polynomial q D b R).eval₂ (Int.castRingHom ℝ) x) =
      (fun x : Fin (n + 4) → ℝ => (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom ℝ) x) ∘ coordinates (n + 3) := by
    funext x
    rw [polynomial, eval₂_rename]
    rfl
  rw [he]
  exact (BoundedRegularSource.proper q D b R).comp (coordinates (n + 3)).isProperMap

theorem regular {n : ℕ} {K : Type*} [Field K] [Algebra ℚ K] (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (x : Fin (n + 4) → K)
    (hx : (polynomial q D b R).eval₂ (Int.castRingHom K) x = 0) :
    ∃ j, (pderiv j (polynomial q D b R)).eval₂ (Int.castRingHom K) x ≠ 0 := by
  have hx' : (BoundedRegularSource.polynomial q D b R).eval₂ (Int.castRingHom K)
      (fun i => x (inputIndex (n + 3) i)) = 0 := by
    simpa only [polynomial, eval₂_rename, Function.comp_def] using hx
  obtain ⟨i, hi⟩ := BoundedRegularSource.regular q D b R hD hb _ hx'
  have hinj : Function.Injective (inputIndex (n + 3)) := (inputEquiv (n + 3)).injective
  refine ⟨inputIndex (n + 3) i, ?_⟩
  simpa only [polynomial, pderiv_rename hinj, eval₂_rename, Function.comp_def] using hi

theorem generated_regular {K : Type*} [Field K] [Algebra ℚ K] (P : BoundedFullWriter.Readers) (c : List Bool)
    (x : Fin (P.dim c + 4) → K)
    (hx : (polynomial (BoundedFullWriter.original P c) (BoundedFullWriter.size P c) (BoundedFullWriter.size P c) (P.radius c)).eval₂
      (Int.castRingHom K) x = 0) :
    ∃ j, (pderiv j (polynomial (BoundedFullWriter.original P c) (BoundedFullWriter.size P c)
      (BoundedFullWriter.size P c) (P.radius c))).eval₂ (Int.castRingHom K) x ≠ 0 :=
  regular _ _ _ _ (BoundedFullWriter.original_degree P c) (BoundedFullWriter.original_mass P c) x hx

end LeanCanny.Encoding.BoundedFullGeometry
