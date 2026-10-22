/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Algebra.MonoidAlgebra.Cardinal
public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Finsupp.Encodable

/-! # Independent real directions in prescribed open intervals

Over a countable coefficient ring embedded in the reals, the algebraic
elements form a countable set. Every nonempty real interval therefore has a
transcendental element. Repeatedly adjoining such elements gives independent
finite tuples inside any prescribed product of nonempty open intervals.
-/

@[expose] public section

namespace LeanCanny.Geometry.IndependentRealDirections
open Set
universe u

theorem countable_algebraic (R : Type*) [CommRing R] [Algebra R ℝ] [Countable R]
    (hinj : Function.Injective (algebraMap R ℝ)) : {x : ℝ | IsAlgebraic R x}.Countable := by
  classical
  let : Countable (Polynomial R) := Cardinal.mk_le_aleph0_iff.mp
    (Polynomial.cardinalMk_le_max.trans (max_le Cardinal.mk_le_aleph0 le_rfl))
  let Z (p : {p : Polynomial R // p ≠ 0}) : Set ℝ :=
    {x | Polynomial.IsRoot (p.val.map (algebraMap R ℝ)) x}
  have hZ (p : {p : Polynomial R // p ≠ 0}) : (Z p).Countable :=
    (Polynomial.finite_setOfPred_isRoot ((Polynomial.map_ne_zero_iff hinj).mpr p.property)).countable
  apply (Set.countable_iUnion hZ).mono
  rintro x ⟨p, hp, he⟩
  refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, ?_⟩
  change Polynomial.eval x (p.map (algebraMap R ℝ)) = 0
  rw [Polynomial.eval_map]
  exact he

theorem exists_transcendental_between (R : Type*) [CommRing R] [Algebra R ℝ] [Countable R]
    (hinj : Function.Injective (algebraMap R ℝ)) (a b : ℝ) (hab : a < b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ Transcendental R x := by
  classical
  by_contra hn
  have hsub : Ioo a b ⊆ {x : ℝ | IsAlgebraic R x} := by
    intro x hx
    by_contra htrans
    exact hn ⟨x, hx.1, hx.2, htrans⟩
  exact (not_le_of_gt hab) (Cardinal.Real.Ioo_countable_iff.mp ((countable_algebraic R hinj).mono hsub))

variable {K : Type*} [Field K] [Algebra K ℝ] [Countable K]

theorem countable_adjoin {ι : Type*} [Countable ι] (v : ι → ℝ) (hv : AlgebraicIndependent K v) :
    Countable (Algebra.adjoin K (Set.range v)) :=
  Countable.of_equiv (MvPolynomial ι K) hv.aevalEquiv.toEquiv

theorem exists_in_intervals (ι : Type u) [Finite ι] (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    ∃ v : ι → ℝ, AlgebraicIndependent K v ∧ ∀ i, a i < v i ∧ v i < b i := by
  classical
  let P (ι : Type u) := ∀ a b : ι → ℝ, (∀ i, a i < b i) →
    ∃ v : ι → ℝ, AlgebraicIndependent K v ∧ ∀ i, a i < v i ∧ v i < b i
  have hP : P ι := by
    apply Finite.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro A B e h a b hab
      obtain ⟨v, hv, hb⟩ := h (a ∘ e) (b ∘ e) (fun i => hab (e i))
      refine ⟨v ∘ e.symm, hv.comp _ e.symm.injective, ?_⟩
      intro i
      simpa only [Function.comp_apply, e.apply_symm_apply] using hb (e.symm i)
    · intro a b _
      exact ⟨PEmpty.elim, algebraicIndependent_empty_type, fun i => PEmpty.elim i⟩
    · intro A _ h a b hab
      obtain ⟨v, hv, hb⟩ := h (fun i => a (some i)) (fun i => b (some i)) (fun i => hab (some i))
      let : Countable (Algebra.adjoin K (Set.range v)) := countable_adjoin v hv
      obtain ⟨x, hxa, hxb, hx⟩ := exists_transcendental_between (Algebra.adjoin K (Set.range v))
        Subtype.val_injective (a none) (b none) (hab none)
      refine ⟨fun i => i.elim x v, (hv.option_iff_transcendental x).mpr hx, ?_⟩
      intro i
      cases i with
      | none => exact ⟨hxa, hxb⟩
      | some i => exact hb i
  exact hP a b hab

end LeanCanny.Geometry.IndependentRealDirections
