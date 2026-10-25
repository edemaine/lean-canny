/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootBranchLocal
public import LeanCanny.Geometry.ProperProjection
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Covering.Basic

/-! # Projection charts on regular root spaces

At every root where the derivative in the unknowns is invertible, projection
to the parameter is a local homeomorphism. The inverse chart is the branch
constructed by the implicit function theorem. This supplies the local
geometric input for turning a proper regular projection into a covering map.
-/

@[expose] public section

namespace LeanCanny.Geometry.RootProjection
open Set Filter Topology
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

abbrev Space (f : ℝ × E → F) := {z : ℝ × E // f z = 0}

def projection (f : ℝ × E → F) (z : Space f) : ℝ := z.val.1

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
@[fun_prop] theorem continuous_projection (f : ℝ × E → F) : Continuous (projection f) :=
  continuous_fst.comp continuous_subtype_val

/-- An actual projection chart around a regular root. It contains all roots
in its source neighborhood, not just a selected root branch. -/
theorem exists_chart (f : ℝ × E → F) (z₀ : Space f)
    (hf : ContDiffAt ℝ 1 f z₀.val)
    (hJac : (fderiv ℝ f z₀.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    ∃ chart : OpenPartialHomeomorph (Space f) ℝ,
      z₀ ∈ chart.source ∧ projection f = chart := by
  classical
  obtain ⟨δ, hδ, curve, hc₀, hc, hroots, huniq⟩ :=
    RootBranchLocal.exists_branch f z₀.val.1 z₀.val.2 hf z₀.property hJac
  obtain ⟨U, hUsub, hU, hzU⟩ := mem_nhds_iff.mp huniq
  have hcAt : ContinuousAt curve z₀.val.1 := hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hpair : ContinuousAt (fun t : ℝ => (t, curve t)) z₀.val.1 := continuousAt_id.prodMk hcAt
  have hpairU : ∀ᶠ t in 𝓝 z₀.val.1, (t, curve t) ∈ U := by
    apply hpair.preimage_mem_nhds
    simpa only [hc₀, Prod.eta] using hU.mem_nhds hzU
  have hsmall : Ioo (z₀.val.1 - δ) (z₀.val.1 + δ) ∈ 𝓝 z₀.val.1 :=
    Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨l, r, hlr, hV⟩ := (hpairU.and hsmall).exists_Ioo_subset
  let V := Ioo l r
  have hVbig : V ⊆ Icc (z₀.val.1 - δ) (z₀.val.1 + δ) :=
    fun t ht => Ioo_subset_Icc_self (hV ht).2
  have hVroot (t : ℝ) (ht : t ∈ V) : f (t, curve t) = 0 := hroots t (hVbig ht)
  let inv : ℝ → Space f := fun t => if ht : t ∈ V then ⟨(t, curve t), hVroot t ht⟩ else z₀
  have hInv : ContinuousOn inv V := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hcurve : Continuous (fun t : V => curve t) :=
      continuousOn_iff_continuous_domRestrict.mp (hc.mono hVbig)
    have hcont : Continuous (fun t : V => (⟨(t.val, curve t), hVroot t t.property⟩ : Space f)) :=
      (continuous_subtype_val.prodMk hcurve).subtype_mk _
    apply hcont.congr
    intro t
    change (⟨(t.val, curve t.val), hVroot t t.property⟩ : Space f) = inv t.val
    simp only [inv, dite_eq_left t.property]
  let chart : OpenPartialHomeomorph (Space f) ℝ := {
    toFun := projection f
    invFun := inv
    source := {z | z.val ∈ U ∧ projection f z ∈ V}
    target := V
    map_source' := fun _ hz => hz.2
    map_target' := by
      intro t ht
      simp only [inv, dite_eq_left ht, mem_ofPred_eq, projection]
      exact ⟨(hV ht).1, ht⟩
    left_inv' := by
      intro z hz
      have hcurve : curve z.val.1 = z.val.2 := (hUsub hz.1).mp z.property
      have hzV : z.val.1 ∈ V := hz.2
      apply Subtype.ext
      simp only [projection, inv, dite_eq_left hzV, hcurve, Prod.eta]
    right_inv' := by
      intro t ht
      simp only [inv, dite_eq_left ht, projection]
    open_source := (hU.preimage continuous_subtype_val).inter
      (isOpen_Ioo.preimage (continuous_projection f))
    open_target := isOpen_Ioo
    continuousOn_toFun := (continuous_projection f).continuousOn
    continuousOn_invFun := hInv }
  refine ⟨chart, ?_, rfl⟩
  exact ⟨hzU, hlr⟩

/-- Projection is a local homeomorphism over any region of regular fibers. -/
theorem isLocalHomeomorphOn (f : ℝ × E → F) (s : Set ℝ)
    (hf : ∀ z : Space f, projection f z ∈ s → ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : Space f, projection f z ∈ s →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    IsLocalHomeomorphOn (projection f) (projection f ⁻¹' s) := by
  intro z hz
  exact exists_chart f z (hf z hz) (hJac z hz)

omit [NormedSpace ℝ E] [CompleteSpace E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- A fixed compact bound on the unknowns makes a closed root family proper
over its parameter. The parameter itself need not range over a compact set. -/
theorem isProperMap_of_compact_bound (f : ℝ × E → F) (hf : Continuous f)
    {K : Set E} (hK : IsCompact K) (hbound : ∀ z : Space f, z.val.2 ∈ K) :
    IsProperMap (projection f) :=
  ProperProjection.isProperMap_fst (isClosed_eq hf continuous_const) hK
    (fun z hz => hbound ⟨z, hz⟩)

/-- A regular fiber is discrete, so properness makes its root set finite. -/
theorem finite_fiber (f : ℝ × E → F) (t : ℝ)
    (hproper : IsProperMap (projection f))
    (hf : ∀ z : Space f, projection f z = t → ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : Space f, projection f z = t →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    (projection f ⁻¹' {t}).Finite := by
  apply (hproper.isCompact_preimage isCompact_singleton).finite
  apply IsDiscrete.of_openPartialHomeomorph (projection f) subset_rfl
  intro z hz
  change projection f z = t at hz
  obtain ⟨chart, hzc, heq⟩ := exists_chart f z (hf z hz) (hJac z hz)
  exact ⟨chart, hzc, heq.symm⟩

/-- Properness and regularity give finitely many roots in each regular fiber,
and projection is a covering there. Finiteness is derived from compactness and
the local charts, rather than assumed as a separate root-enumeration oracle. -/
theorem isCoveringMapOn (f : ℝ × E → F) (s : Set ℝ)
    (hproper : IsProperMap (projection f))
    (hf : ∀ z : Space f, projection f z ∈ s → ContDiffAt ℝ 1 f z.val)
    (hJac : ∀ z : Space f, projection f z ∈ s →
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible) :
    IsCoveringMapOn (projection f) s := by
  have hlocal := isLocalHomeomorphOn f s hf hJac
  apply hproper.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn _ hlocal
  intro t ht
  exact finite_fiber f t hproper
    (fun z hz => hf z (by rw [hz]; exact ht)) (fun z hz => hJac z (by rw [hz]; exact ht))

end LeanCanny.Geometry.RootProjection
