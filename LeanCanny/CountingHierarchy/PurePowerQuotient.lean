/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerResidueRelations
public import LeanCanny.Algebra.MonicMonomialReduction
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The quotient and its spanning normal monomials

The finite residue descends to the actual relation ideal. Every quotient
class is spanned by the monomials with coordinate exponents below `ell`:
a divisible pure power can be replaced by its lower part, strictly
decreasing total degree. This spanning proof assumes no quotient basis.
-/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical BigOperators

variable {S : Type*} [CommRing S] {n : ℕ}

abbrev QuotientAlgebra (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :=
  MvPolynomial (Fin n) S ⧸ relationIdeal ell r

@[expose] noncomputable def projection (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    MvPolynomial (Fin n) S →ₐ[S] QuotientAlgebra ell r :=
  Ideal.Quotient.mkₐ S (relationIdeal ell r)

theorem projection_surjective (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    Function.Surjective (projection ell r) := Ideal.Quotient.mk_surjective

theorem projection_eq_zero_iff (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (v : MvPolynomial (Fin n) S) : projection ell r v = 0 ↔ v ∈ relationIdeal ell r :=
  Ideal.Quotient.eq_zero_iff_mem

theorem projection_X_pow (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) (i : Fin n) :
    (projection ell r (X i)) ^ ell = projection ell r (r i) := by
  apply sub_eq_zero.mp
  rw [← map_pow, ← map_sub, projection_eq_zero_iff]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The residue on the actual quotient, using its proved ideal vanishing. -/
@[expose] noncomputable def quotientFunctional {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    QuotientAlgebra ell r →ₗ[S] S :=
  ((relationIdeal ell r).restrictScalars S).liftQ (linear hell r hr)
    (fun q hq => linear_mem_ideal hell r hr q hq)

@[simp] theorem quotientFunctional_projection {ell : ℕ} (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) :
    quotientFunctional hell r hr (projection ell r v) = residue ell r v := rfl

abbrev NormalIndex (n ell : ℕ) := Fin n → Fin ell

@[expose] noncomputable def boxExponent {ell : ℕ} (a : NormalIndex n ell) : Fin n →₀ ℕ :=
  exponent (fun i => (a i).val)

@[simp] theorem boxExponent_apply {ell : ℕ} (a : NormalIndex n ell) (i : Fin n) :
    boxExponent a i = (a i).val := rfl

@[expose] noncomputable def normalClass (ell : ℕ)
    (r : Fin n → MvPolynomial (Fin n) S) (a : NormalIndex n ell) : QuotientAlgebra ell r :=
  projection ell r (monomial (boxExponent a) 1)

theorem projection_monomial_smul (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (e : Fin n →₀ ℕ) (c : S) :
    projection ell r (monomial e c) = c • projection ell r (monomial e 1) := by
  rw [← map_smul]
  simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- Degree induction expresses every monomial through normal classes. -/
theorem monomial_mem_normal_span {ell : ℕ}
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (e : Fin n →₀ ℕ) :
    projection ell r (monomial e 1) ∈ Submodule.span S (Set.range (normalClass ell r)) := by
  let U := Submodule.span S (Set.range (normalClass ell r))
  suffices ∀ d (e : Fin n →₀ ℕ), e.degree = d →
      projection ell r (monomial e 1) ∈ U by
    exact this e.degree e rfl
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro e he
    by_cases hnormal : ∀ i, e i < ell
    · let a : NormalIndex n ell := fun i => ⟨e i, hnormal i⟩
      have ha : boxExponent a = e := by ext i; rfl
      apply Submodule.subset_span
      refine ⟨a, ?_⟩
      rw [normalClass, ha]
    · obtain ⟨i, hi⟩ : ∃ i, ell ≤ e i := by
        simpa only [not_forall, not_lt] using hnormal
      let e' := LeanCanny.Algebra.MonicMonomialReduction.residual e i ell
      let q : MvPolynomial (Fin n) S := monomial e' 1 * r i
      have hdeg : q.totalDegree < d := by
        have hmul := MvPolynomial.totalDegree_mul (monomial e' (1 : S)) (r i)
        have hmono : (monomial e' (1 : S)).totalDegree ≤ e'.degree :=
          MvPolynomial.totalDegree_monomial_le _ _
        have hres := LeanCanny.Algebra.MonicMonomialReduction.residual_degree e i ell hi
        have hlo := hr i
        change q.totalDegree < d
        dsimp only [q]
        change e'.degree + ell = e.degree at hres
        omega
      have hm : monomial e' (1 : S) * X i ^ ell = monomial e 1 := by
        rw [← monomial_add_single]
        exact congrArg (fun a => monomial a (1 : S))
          (LeanCanny.Algebra.MonicMonomialReduction.residual_add e i ell hi)
      have hp : projection ell r (monomial e 1) = projection ell r q := by
        calc
          _ = projection ell r (monomial e' 1) * (projection ell r (X i)) ^ ell := by
            rw [← hm, map_mul, map_pow]
          _ = projection ell r (monomial e' 1) * projection ell r (r i) := by
            rw [projection_X_pow]
          _ = _ := (map_mul (projection ell r) _ _).symm
      rw [hp, q.as_sum, map_sum]
      apply U.sum_mem
      intro m hm
      have hmdeg : m.degree < d :=
        (MvPolynomial.le_totalDegree hm).trans_lt hdeg
      rw [projection_monomial_smul]
      exact U.smul_mem (q.coeff m) (ih m.degree hmdeg m rfl)

/-- Normal monomials span the whole quotient over the original coefficient ring. -/
theorem normal_span_eq_top {ell : ℕ}
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    Submodule.span S (Set.range (normalClass ell r)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro a
  obtain ⟨v, rfl⟩ := projection_surjective ell r a
  induction v using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [projection_monomial_smul]
    exact Submodule.smul_mem _ c (monomial_mem_normal_span r hr e)
  | add v w hv hw =>
    rw [map_add]
    exact Submodule.add_mem _ hv hw

end LeanCanny.CountingHierarchy.PurePowerResidue
