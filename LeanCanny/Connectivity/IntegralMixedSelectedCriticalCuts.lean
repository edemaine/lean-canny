/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.IntegralMixedSelectedCriticalArcs
public import LeanCanny.Algebra.IntegralMixedRelativeCuts
/-! # One original-source cut ceiling supplies the selected-parent arc intervals -/
@[expose] public section
namespace LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedSelectedGeometry IntegralMixedSelectedCriticalArcs
open IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev Tag (r : Rule n) := Fin 3 × Free r

def kind (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ) (j : Tag r) : Kind P r :=
  if j.1 = 0 then .coordinate j.2 (c.coordinateIndex j.2) else
    if j.1 = 1 then .squarefree j.2 (c.squarefreeIndex j.2) else .value j.2 (c.valueIndex j.2)

theorem kind_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ) (j : Tag r) :
    Valid x hm r φ (kind x hm r φ c j) := by
  obtain ⟨i,j⟩ := j
  fin_cases i
  · exact c.coordinateValid j
  · exact c.squarefreeValid j
  · exact c.valueValid j

noncomputable def cut (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ) (j : Tag r) :=
  factor x hm r (kind x hm r φ c j)

theorem cut_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ) (j : Tag r) :
    (cut x hm r φ c j).natDegree ≤ IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree :=
  factor_degree x hm r _

def bad (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ) : Set ℝ :=
  {t | ∃ j, (cut x hm r φ c j).eval₂ φ.toRingHom t = 0}

theorem finite_bad (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ) : (bad x hm r φ c).Finite := by
  have H := Set.finite_iUnion (fun j : Tag r => finite_cuts x hm r φ (kind x hm r φ c j) (kind_valid x hm r φ c j))
  exact H.subset (fun _ ht => Set.mem_iUnion.mpr ht)

def Anchored (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a b : ℝ) (t₀ : Ioo a b) : Prop :=
    Finite (Fiber x hm r φ t₀.val) ∧
    ∃ curve : Fiber x hm r φ t₀.val → ℝ → Free r → ℝ,
      (∀ j, curve j t₀.val = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → original x hm r φ (t,curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ z, original x hm r φ (t.val,z) = 0 ↔ ∃! j, curve j t.val = z) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t,curve j t)) '' Ioo a b)

theorem anchored_arcs (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (c : Choices x hm r φ)
    (a b : ℝ) (t₀ : Ioo a b) (havoid : ∀ t ∈ Ioo a b, t ∉ bad x hm r φ c) : Anchored x hm r φ a b t₀ := by
  apply IntegralMixedSelectedCriticalArcs.anchored_arcs x hm r φ c.squarefreeIndex c.squarefreeValid c.valueIndex c.valueValid a b t₀
  · intro t ht j HZ
    exact havoid t ht ⟨(1,j), HZ⟩
  · intro t ht j HZ
    exact havoid t ht ⟨(2,j), HZ⟩

theorem exists_anchored_arcs (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ∃ c : Choices x hm r φ, (bad x hm r φ c).Finite ∧ ∀ (a b : ℝ) (t₀ : Ioo a b),
      (∀ t ∈ Ioo a b, t ∉ bad x hm r φ c) → Anchored x hm r φ a b t₀ := by
  obtain ⟨c⟩ := exists_choices x hm r φ
  exact ⟨c, finite_bad x hm r φ c, fun a b t₀ => anchored_arcs x hm r φ c a b t₀⟩

end LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
