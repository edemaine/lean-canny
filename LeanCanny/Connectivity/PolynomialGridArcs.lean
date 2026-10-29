/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.SquarefreeRootArcs
public import LeanCanny.Connectivity.AlgebraicArcFilter

/-! # Complete original polynomial arcs from a proper coordinate grid

Nonzero integer coordinate equations capture the original polynomial system.
Constructed squarefree and polynomial-value exceptional sets split the
parameter line into intervals on which a single original fiber indexes
complete original arcs. Every endpoint satisfies the original equations.
Original roots and coordinate equations may be singular or repeated.

Properness of the coordinate grid and the capture relation are explicit
hypotheses. The test-value annihilators and combined finite exceptional set
are constructed qualitatively; their native coefficient readers and size
bounds are not provided here.
-/

@[expose] public section
namespace LeanCanny.Connectivity.PolynomialGridArcs
open Set Geometry LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

abbrev Fiber (q : κ → MvPolynomial ι (Polynomial ℝ)) (t : ℝ) :=
  {x : ι → ℝ // PolynomialGridValues.value q (t, x) = 0}

/-- One actual original root in the indexing fiber labels each retained arc.
Neither original-system regularity nor simple coordinate roots are assumed. -/
theorem exists_anchored_arcs (p : ι → Polynomial (Polynomial ℤ)) (hp : ∀ i, p i ≠ 0)
    (q : κ → MvPolynomial ι (Polynomial ℝ))
    (hproper : IsProperMap (RootProjection.projection (SquarefreeRootFamily.value p)))
    (hcapture : ∀ t x, PolynomialGridValues.value q (t, x) = 0 →
      SquarefreeRootFamily.value p (t, x) = 0) :
    ∃ bad : Set ℝ, bad.Finite ∧ ∀ (a b : ℝ) (t₀ : Ioo a b),
      (∀ t ∈ Ioo a b, t ∉ bad) →
      Finite (Fiber q t₀.val) ∧
      ∃ curve : Fiber q t₀.val → ℝ → ι → ℝ,
        (∀ j, curve j t₀.val = j.val) ∧
        (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
        (∀ j t, t ∈ Icc a b → PolynomialGridValues.value q (t, curve j t) = 0) ∧
        (∀ t : Ioo a b, ∀ x, PolynomialGridValues.value q (t.val, x) = 0 ↔
          ∃! j, curve j t.val = x) ∧
        ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  obtain ⟨Q, _, hfiniteQ, hrelQ⟩ := PolynomialGridValues.exists_annihilators
    (fun i => SquarefreeRootFamily.realPolynomial (p i))
    (fun i => SquarefreeRootFamily.realPolynomial_ne_zero (hp i)) q
  let exceptional : Set ℝ := {t | ∃ i, SymbolicScaledSquarefree.scalarEvaluation t
    (SymbolicScaledSquarefree.exceptional (p i)) = 0}
  let testExceptional : Set ℝ := {t | ∃ k, (Q k).trailingCoeff.eval t = 0}
  refine ⟨exceptional ∪ testExceptional,
    (SquarefreeRootFamily.finite_exceptional p hp).union hfiniteQ, ?_⟩
  intro a b t₀ havoid
  have havoidP (t : ℝ) (ht : t ∈ Ioo a b) (i : ι) : SymbolicScaledSquarefree.scalarEvaluation t
      (SymbolicScaledSquarefree.exceptional (p i)) ≠ 0 :=
    fun hz => havoid t ht (Or.inl ⟨i, hz⟩)
  have havoidQ (k : κ) (t : ℝ) (ht : t ∈ Ioo a b) : (Q k).trailingCoeff.eval t ≠ 0 :=
    fun hz => havoid t ht (Or.inr ⟨k, hz⟩)
  obtain ⟨hfinite, branch, _, hcont, hgridroot, hgridcomplete, _⟩ :=
    SquarefreeRootArcs.exists_anchored_arcs p hp a b t₀ hproper havoidP
  let I := RootBranches.Index
    (SquarefreeRootFamily.value (fun i => SymbolicScaledSquarefree.polynomial (p i))) a b t₀
  let : Finite I := hfinite
  have hrel (j : I) (k : κ) (t : ℝ) (ht : t ∈ Ioo a b) :
      (Q k).eval₂ (Polynomial.evalRingHom t) (PolynomialGridValues.value q (t, branch j t) k) = 0 := by
    apply hrelQ t (branch j t) _ k
    intro i
    rw [SquarefreeRootFamily.eval_realPolynomial]
    have H := congrFun (hgridroot j t (Ioo_subset_Icc_self ht)) i
    rwa [SquarefreeRootFamily.value_apply, Pi.zero_apply] at H
  have hcover (t : Ioo a b) (x : ι → ℝ) (hx : PolynomialGridValues.value q (t.val, x) = 0) :
      ∃! j : I, branch j t.val = x :=
    (hgridcomplete t x).mp (hcapture t.val x hx)
  obtain ⟨hc, hroots, hcomplete, haccess⟩ := AlgebraicArcFilter.filtered_arcs
    (PolynomialGridValues.value q) (PolynomialGridValues.continuous_value q) a b t₀ branch hcont
    hcover Q hrel havoidQ
  let S := AlgebraicArcFilter.Label (PolynomialGridValues.value q) branch t₀.val
  let : Finite S := Finite.of_injective (fun j : S => (j.val : I)) (fun _ _ h => Subtype.ext h)
  let point : S → Fiber q t₀.val := fun j =>
    ⟨branch j.val t₀.val, hroots j t₀.val (Ioo_subset_Icc_self t₀.property)⟩
  have hbij : Function.Bijective point := by
    constructor
    · intro j k hjk
      obtain ⟨l, _, huniq⟩ := (hcomplete t₀ (branch j.val t₀.val)).mp
        (hroots j t₀.val (Ioo_subset_Icc_self t₀.property))
      exact (huniq j rfl).trans (huniq k (congrArg Subtype.val hjk).symm).symm
    · intro x
      obtain ⟨j, hj, _⟩ := (hcomplete t₀ x.val).mp x.property
      exact ⟨j, Subtype.ext hj⟩
  let e : S ≃ Fiber q t₀.val := Equiv.ofBijective point hbij
  have hfiber : Finite (Fiber q t₀.val) := Finite.of_surjective point hbij.surjective
  refine ⟨hfiber, (fun x => branch (e.symm x).val), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact congrArg Subtype.val (e.apply_symm_apply x)
  · intro x
    exact hc (e.symm x)
  · intro x t ht
    exact hroots (e.symm x) t ht
  · intro t x
    constructor
    · intro hx
      obtain ⟨j, hj, huniq⟩ := (hcomplete t x).mp hx
      refine ⟨e j, ?_, ?_⟩
      · simpa only [e.symm_apply_apply] using hj
      · intro k hk
        have H := congrArg e (huniq (e.symm k) hk)
        simpa only [e.apply_symm_apply] using H
    · rintro ⟨j, hj, _⟩
      rw [← hj]
      exact hroots (e.symm j) t.val (Ioo_subset_Icc_self t.property)
  · intro x
    exact haccess (e.symm x)

end LeanCanny.Connectivity.PolynomialGridArcs
