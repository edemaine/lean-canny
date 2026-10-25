/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootBranches
public import LeanCanny.Geometry.AlgebraicBranchLimit
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Interval.Set.Infinite

/-! # Counting branches by coordinate equations

Nonzero univariate equations for the coordinates of a root fiber bound its
cardinality by the product of their degrees. Since a regular interval's
branches are indexed by one fiber, the same bound counts all its branches.
The coordinate equations must still be constructed with controlled degrees;
this result does not bound their coefficient encodings or compute the roots.
-/

@[expose] public section

namespace LeanCanny.Geometry.RootBranchCount
open Set Polynomial Function

variable {ι Z : Type*} [Fintype ι]

/-- Coordinate equations bound any injectively represented collection of points. -/
theorem finite_card_le (coord : Z → ι → ℝ) (hinj : Injective coord)
    (q : ι → Polynomial ℝ) (hq : ∀ i, q i ≠ 0)
    (hzero : ∀ z i, (q i).eval (coord z i) = 0) :
    Finite Z ∧ Nat.card Z ≤ ∏ i, (q i).natDegree := by
  classical
  let R : ι → Type := fun i => {x : ℝ // x ∈ (q i).roots.toFinset}
  let enc : Z → ∀ i, R i := fun z i =>
    ⟨coord z i, Multiset.mem_toFinset.mpr ((mem_roots (hq i)).mpr (hzero z i))⟩
  have henc : Injective enc := by
    intro z w h
    apply hinj
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hfin : Finite Z := Finite.of_injective enc henc
  refine ⟨hfin, ?_⟩
  calc
    Nat.card Z ≤ Nat.card (∀ i, R i) := Nat.card_le_card_of_injective enc henc
    _ = ∏ i, Nat.card (R i) := Nat.card_pi
    _ ≤ ∏ i, (q i).natDegree := by
      apply Finset.prod_le_prod
      intro i _
      change Nat.card {x : ℝ // x ∈ (q i).roots.toFinset} ≤ (q i).natDegree
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact (Multiset.toFinset_card_le _).trans (card_roots' _)

variable {F : Type*} [NormedAddCommGroup F]

/-- Specialize the parameter, retaining a polynomial in the coordinate. -/
noncomputable def specialize (p : Polynomial (Polynomial ℝ)) (t : ℝ) : Polynomial ℝ :=
  (Bivariate.swap p).map (evalRingHom t)

theorem eval_specialize (p : Polynomial (Polynomial ℝ)) (t x : ℝ) :
    (specialize p t).eval x = AlgebraicBranchLimit.value p t x := by
  rw [specialize, map_evalRingHom_eval]
  have hswap := Bivariate.aevalAeval_swap (R := ℝ) t x p
  simp only [coe_aevalAeval_eq_evalEval] at hswap
  rw [hswap, AlgebraicBranchLimit.value, eval₂_evalRingHom]

/-- A nonzero bivariate equation vanishes identically in the coordinate at
only finitely many parameter values. Singular values remain allowed. -/
theorem finite_bad_specializations (p : Polynomial (Polynomial ℝ)) (hp : p ≠ 0) :
    {t | specialize p t = 0}.Finite := by
  have hswap : Bivariate.swap p ≠ 0 := by
    intro h
    apply hp
    apply Bivariate.swap.injective
    simpa only [map_zero] using h
  apply (finite_setOfPred_isRoot (leadingCoeff_ne_zero.mpr hswap)).subset
  intro t ht
  have hz := congrArg (fun q : Polynomial ℝ => q.coeff (Bivariate.swap p).natDegree) ht
  change (Bivariate.swap p).leadingCoeff.eval t = 0
  simpa only [specialize, coeff_map, coeff_zero, coe_evalRingHom, coeff_natDegree] using hz

/-- Every nonempty open interval contains a simultaneous good specialization
for any finite family of nonzero coordinate equations. -/
theorem exists_nondegenerate_sample {a b : ℝ} (hab : a < b)
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0) :
    ∃ t : Ioo a b, ∀ i, specialize (p i) t.val ≠ 0 := by
  have hfin : (⋃ i, {t | specialize (p i) t = 0}).Finite :=
    Set.finite_iUnion (fun i => finite_bad_specializations (p i) (hp i))
  obtain ⟨t, ht, hbad⟩ := (Ioo_infinite hab).exists_notMem_finite hfin
  refine ⟨⟨t, ht⟩, ?_⟩
  intro i hz
  exact hbad (mem_iUnion.mpr ⟨i, hz⟩)

/-- A branch count needs equations only on one fiber. Properness and
regularity are needed for the branch enumeration, not for this finite bound. -/
theorem finite_card_index_le (f : ℝ × (ι → ℝ) → F) (a b : ℝ) (t₀ : Ioo a b)
    (q : ι → Polynomial ℝ) (hq : ∀ i, q i ≠ 0)
    (hzero : ∀ x, f (t₀.val, x) = 0 → ∀ i, (q i).eval (x i) = 0) :
    Finite (RootBranches.Index f a b t₀) ∧
      Nat.card (RootBranches.Index f a b t₀) ≤ ∏ i, (q i).natDegree := by
  let coord : RootBranches.Index f a b t₀ → ι → ℝ := fun j => j.val.val.val.2
  have hparam (j : RootBranches.Index f a b t₀) : j.val.val.val.1 = t₀.val :=
    congrArg Subtype.val j.property
  apply finite_card_le coord
  · intro i j hij
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ((hparam i).trans (hparam j).symm) hij
  · exact hq
  · intro j i
    have hz := j.val.val.property
    have hp : j.val.val.val = (t₀.val, coord j) := Prod.ext (hparam j) rfl
    rw [hp] at hz
    exact hzero (coord j) hz i

/-- Nonzero bivariate coordinate equations give an explicit degree bound on
an indexing fiber chosen inside the interval. The degrees are taken in the
coordinate variable, and specialization cannot increase them. -/
theorem exists_fiber_bound (f : ℝ × (ι → ℝ) → F) {a b : ℝ} (hab : a < b)
    (p : ι → Polynomial (Polynomial ℝ)) (hp : ∀ i, p i ≠ 0)
    (hzero : ∀ t ∈ Ioo a b, ∀ x, f (t, x) = 0 →
      ∀ i, AlgebraicBranchLimit.value (p i) t (x i) = 0) :
    ∃ t₀ : Ioo a b, Finite (RootBranches.Index f a b t₀) ∧
      Nat.card (RootBranches.Index f a b t₀) ≤ ∏ i, (Bivariate.swap (p i)).natDegree := by
  classical
  obtain ⟨t₀, ht₀⟩ := exists_nondegenerate_sample hab p hp
  have hbound := finite_card_index_le f a b t₀ (fun i => specialize (p i) t₀.val) ht₀
    (fun x hx i => (eval_specialize (p i) t₀.val (x i)).trans (hzero t₀.val t₀.property x hx i))
  refine ⟨t₀, hbound.1, hbound.2.trans ?_⟩
  exact Finset.prod_le_prod (fun i _ => natDegree_map_le)

end LeanCanny.Geometry.RootBranchCount
