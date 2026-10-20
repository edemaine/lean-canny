/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-! # Active constraints at a maximum and normalized Lagrange multipliers

Strictly positive inactive constraints remain positive near the maximum.
Consequently a maximum on an inequality set is a local maximum on the fiber
of its active equalities. A surjective constraint derivative then makes the
objective multiplier nonzero, yielding normalized Lagrange multipliers.
-/

@[expose] public section

namespace LeanCanny.Geometry.ActiveExtremum

section LocalMaximum
variable {E I : Type*} [TopologicalSpace E] [Fintype I]

def feasible (g : E → I → ℝ) (r : E → ℝ) : Set E := {x | (∀ i, 0 ≤ g x i) ∧ r x = 0}

def activeMap (g : E → I → ℝ) (r : E → ℝ) (s : Finset I) (x : E) : (s → ℝ) × ℝ :=
  (fun i => g x i, r x)

theorem isLocalMaxOn_fiber (g : E → I → ℝ) (r φ : E → ℝ) (s : Finset I) (z : E)
    (hz : z ∈ feasible g r) (hg : ∀ i, ContinuousAt (fun x => g x i) z)
    (hinactive : ∀ i, i ∉ s → 0 < g z i) (hmax : IsMaxOn φ (feasible g r) z) :
    IsLocalMaxOn φ {x | activeMap g r s x = activeMap g r s z} z := by
  classical
  have hpos : ∀ᶠ x in nhds z, ∀ i, i ∉ s → 0 < g x i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i ∈ s
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hn hi))
    · filter_upwards [(hg i).eventually (isOpen_Ioi.mem_nhds (hinactive i hi))] with x hx
      exact fun _ => hx
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx he
  apply hmax
  constructor
  · intro i
    by_cases hi : i ∈ s
    · have hsame := congrArg (fun v : (s → ℝ) × ℝ => v.1 ⟨i, hi⟩) he
      exact (show g x i = g z i from hsame).symm ▸ hz.1 i
    · exact (hx i hi).le
  · exact (congrArg Prod.snd he).trans hz.2

end LocalMaximum

section Multipliers
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_normalized (f : E → F) (φ : E → ℝ) (z : E)
    (D : E →L[ℝ] F) (L : E →L[ℝ] ℝ)
    (hmax : IsLocalMaxOn φ {x | f x = f z} z)
    (hf : HasStrictFDerivAt f D z) (hφ : HasStrictFDerivAt φ L z)
    (hD : Function.Surjective D) :
    ∃ Λ : Module.Dual ℝ F, ∀ h, L h = Λ (D h) := by
  have hextr : IsLocalExtrOn φ {x | f x = f z} z := Or.inr hmax
  obtain ⟨Λ, c, hn, he⟩ := hextr.exists_linear_map_of_hasStrictFDerivAt hf hφ
  have hc : c ≠ 0 := by
    intro hc
    have hΛ : Λ = 0 := by
      ext b
      obtain ⟨h, rfl⟩ := hD b
      change Λ (D h) = 0
      simpa only [hc, zero_smul, add_zero] using he h
    exact hn (Prod.ext hΛ hc)
  refine ⟨(-c⁻¹) • Λ, ?_⟩
  intro h
  change L h = -c⁻¹ * Λ (D h)
  have hv : L h = -Λ (D h) / c := (eq_div_iff hc).mpr (by
    have hh := he h
    simp only [smul_eq_mul] at hh
    linarith)
  simpa only [div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using hv

end Multipliers
end LeanCanny.Geometry.ActiveExtremum
