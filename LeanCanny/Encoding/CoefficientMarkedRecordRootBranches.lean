/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCartesianRows
public import LeanCanny.Encoding.CoefficientMarkedRecordFullRealization
/-! # Coherent finite branches of the actual full row system

Actual Cartesian labels are restricted by the actual rows at one anchor.
Those same labels cover every row root, including singular roots, throughout
the interval. At dyadic radii the full tuples obtain fresh native words.
-/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
open LeanCanny.Algebra LeanCanny.Computation Polynomial Set
open LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def RowsAt (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (β : ℝ) (z : Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count → ℝ) : Prop :=
  ∀ i, ((CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).rows i).eval₂
    (SymbolicScaledSquarefree.scalarEvaluation β) z = 0

noncomputable abbrev GridIndex (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (a b : ℝ) (s : Ioo a b) :=
  ParameterizedCartesianBranches.Index (CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk []) a b s

noncomputable abbrev Curve (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    (a b : ℝ) (s : Ioo a b) :=
  GridIndex hn ht ha ctx k hk a b s → C(Ioo a b, Fin (CoefficientMarkedRecordRows.symbolic hn ht ha ctx k hk).count → ℝ)

noncomputable def RootIndex (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    {a b : ℝ} (s : Ioo a b) (curve : Curve hn ht ha ctx k hk a b s) :=
  {l : GridIndex hn ht ha ctx k hk a b s // RowsAt hn ht ha ctx k hk s.val (curve l s)}

private theorem finite_grid (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ a) (s : Ioo a b) :
    Finite (GridIndex hn ht ha ctx k hk a b s) := by
  have hp := CoefficientMarkedRecordFullHeadBounds.positive_degree hn ht ha ctx k hk []
  have hd : ∀ i, (CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk [] i).natDegree ≤
      CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx := by
    intro i
    exact (CoefficientMarkedRecordFullHeadBounds.target_degree_le hn ht ha ctx k hk [] i).trans
      (Nat.add_le_add_right (CoefficientMarkedRecordFullHeadControls.dimension_le_budget hn ht ha ctx k hk []) 1)
  have hm : ∀ i j, coefficientMass ((CoefficientMarkedRecordFullHeads.polynomial hn ht ha ctx k hk [] i).coeff j) ≤
      2 ^ CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx := by
    intro i j
    exact (CoefficientMarkedRecordFullHeadControls.coefficient_degree_mass hn ht ha ctx k hk [] i j).2.trans
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  apply ParameterizedCartesianBranches.finite_index _
    (CoefficientMarkedRecordCartesianRows.headDegree hn ht ha ctx)
    (CoefficientMarkedRecordRowDegree.spatialDegree hn ht ha ctx)
    (CoefficientMarkedRecordCartesianRows.mass hn ht ha ctx) hp hd hm _ s
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (CoefficientMarkedRecordCartesianRows.cartesian_cutoff_le hn ht ha ctx k hk)).trans ha0

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedRecordFullHeads.polynomial

/-- A finite, coherent family covers EVERY actual symbolic row root at every
parameter in the interval; its labels are selected from one actual Cartesian family. -/
theorem exists_branches (ctx : List Bool) (k : ℕ) (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx)
    {a b : ℝ} (ha0 : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ a) (s : Ioo a b) :
    ∃ curve : Curve hn ht ha ctx k hk a b s,
      Finite (RootIndex hn ht ha ctx k hk s curve) ∧
      (∀ l : RootIndex hn ht ha ctx k hk s curve, ∀ u : Ioo a b, RowsAt hn ht ha ctx k hk u.val (curve l.val u)) ∧
      (∀ u : Ioo a b, ∀ z, RowsAt hn ht ha ctx k hk u.val z ↔
        ∃! l : RootIndex hn ht ha ctx k hk s curve, curve l.val u = z) := by
  obtain ⟨curve, _, hcover, hrows⟩ := CoefficientMarkedRecordCartesianRows.exists_branches hn ht ha ctx k hk ha0 s
  let : Finite (GridIndex hn ht ha ctx k hk a b s) := finite_grid hn ht ha ctx k hk ha0 s
  refine ⟨curve, by unfold RootIndex; infer_instance, ?_, ?_⟩
  · intro l u
    exact (hrows l.val s u).mp l.property
  · intro u z
    constructor
    · intro hz
      have hh := CoefficientMarkedRecordRowDegree.heads_root hn ht ha ctx k hk [] u.val z hz
      obtain ⟨l, he, hu⟩ := (hcover u z).mp hh
      have hl : RowsAt hn ht ha ctx k hk s.val (curve l s) := (hrows l u s).mp (he.symm ▸ hz)
      refine ⟨⟨l, hl⟩, he, ?_⟩
      intro j hj
      exact Subtype.ext (hu j.val hj)
    · rintro ⟨l, he, _⟩
      exact he ▸ (hrows l.val s u).mp l.property

/-- At every actual requested dyadic radius, EACH constructed full-system branch
is realized by its own exact-width installed native word with the same full tuple. -/
theorem exists_full_branches (ctx : List Bool) {a b : ℝ}
    (ha0 : (2 : ℝ)^CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ a) (s : Ioo a b) :
    ∃ curve : Curve hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl a b s,
      Finite (RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve) ∧
      (∀ u : Ioo a b, ∀ z, RowsAt hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl u.val z ↔
        ∃! l : RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve, curve l.val u = z) ∧
      (∀ l : RootIndex hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl s curve,
        ∀ {R : List Bool → ℕ} (hR : BinaryFn R), CoefficientMarkedRecordCartesianRows.cutoff hn ht ha ctx ≤ R ctx →
        ∀ u : Ioo a b, u.val = (2 : ℝ)^R ctx →
        ∃ w, ∃ hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
          (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w,
          w.length = SquareSampleCompleteVertices.width (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
            (IntegralMixedPhysicalMarkedTest.sampleContext ctx) ∧
          HEq (SquareSampleCompleteVertices.candidate (IntegralMixedPhysicalMarkedTest.input hn ht ha hR false)
            (IntegralMixedPhysicalMarkedTest.sampleContext ctx) w hv).val (curve l.val u)) := by
  obtain ⟨curve, hf, hr, hc⟩ := exists_branches hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl ha0 s
  refine ⟨curve, hf, hc, ?_⟩
  intro l R hR hlarge u hu
  apply CoefficientMarkedRecordFullRealization.exists_word hn ht ha ctx hR
    ((CoefficientMarkedRecordCartesianRows.effectiveCutoff_le hn ht ha ctx).trans hlarge) (curve l.val u)
  exact hu ▸ hr l u

end LeanCanny.Encoding.CoefficientMarkedRecordRootBranches
