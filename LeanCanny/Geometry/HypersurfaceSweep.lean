/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RegularComponentTransport

/-! # Sweeping a fixed hypersurface

Restrict the combined map `(q, g)` to a fixed level of `q` and a region of
sweep values. Its implicit charts become genuine local products for the
sweep on that hypersurface. A proper level function makes the hypersurface
compact, so every continuous sweep on it is proper. Regularity is needed
only on the chosen sweep region, not at its critical endpoints.
-/

@[expose] public section

namespace LeanCanny.Geometry.HypersurfaceSweep
open Set Topology

section Topology
variable {X : Type*} [TopologicalSpace X]

abbrev Level (q : X → ℝ) (c : ℝ) := q ⁻¹' {c}

def projection (q g : X → ℝ) (c : ℝ) : Level q c → ℝ := fun x => g x.val

abbrev Slab (q g : X → ℝ) (c : ℝ) (S : Set ℝ) := projection q g c ⁻¹' S

def combined (q g : X → ℝ) : X → ℝ × ℝ := fun x => (q x, g x)

def region (c : ℝ) (S : Set ℝ) : Set (ℝ × ℝ) := {c} ×ˢ S

/-- Restricting first to the hypersurface, then to sweep values, is the same
topological subspace as restricting the combined map to a product region. -/
def slabHomeomorph (q g : X → ℝ) (c : ℝ) (S : Set ℝ) :
    Slab q g c S ≃ₜ (combined q g ⁻¹' region c S) where
  toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
  invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The fixed first coordinate contributes no extra base dimension. -/
def regionHomeomorph (c : ℝ) (S : Set ℝ) : region c S ≃ₜ S where
  toFun := fun x => ⟨x.val.2, x.property.2⟩
  invFun := fun t => ⟨(c, t.val), rfl, t.property⟩
  left_inv := by
    intro x
    apply Subtype.ext
    exact Prod.ext x.property.1.symm rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_snd.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_const.prodMk continuous_subtype_val).subtype_mk _

theorem isProperMap (q g : X → ℝ) (c : ℝ) (hq : IsProperMap q) (hg : Continuous g) :
    IsProperMap (projection q g c) := by
  let : CompactSpace (Level q c) := isCompact_iff_compactSpace.mp (hq.isCompact_preimage isCompact_singleton)
  exact (hg.comp continuous_subtype_val).isProperMap

end Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual implicit charts of the combined map give a product atlas for a
sweep on the fixed hypersurface. No manifold chart or trivialization is input. -/
theorem exists_charts (q g : E → ℝ) (c : ℝ) (S : Set ℝ)
    (hf : ∀ x, q x = c → g x ∈ S → ContDiffAt ℝ 1 (combined q g) x)
    (hregular : ∀ x, q x = c → g x ∈ S → Function.Surjective (fderiv ℝ (combined q g) x)) :
    ∃ chart : ∀ x : Slab q g c S,
        OpenPartialHomeomorph (Slab q g c S) (S × (fderiv ℝ (combined q g) x.val.val).ker),
      (∀ x, x ∈ (chart x).source) ∧
        ∀ a x, x ∈ (chart a).source → (chart a x).1 = S.restrictPreimage (projection q g c) x := by
  obtain ⟨atlas, hsource, hfirst⟩ := RegularComponentTransport.exists_charts (combined q g) (region c S)
    (fun x hx => hf x hx.1 hx.2) (fun x hx => hregular x hx.1 hx.2)
  apply LocalProductFibers.exists_transported_charts (S.restrictPreimage (projection q g c))
    ((region c S).restrictPreimage (combined q g)) (slabHomeomorph q g c S)
    (regionHomeomorph c S).symm atlas hsource hfirst
  intro x
  exact Subtype.ext rfl

/-- Fiber-component connection persists with both endpoints moving on the
fixed hypersurface. Its proof uses the constructed sweep atlas and properness. -/
theorem isClopen_joined_along (q g : E → ℝ) (c : ℝ) (S : Set ℝ)
    (hq : IsProperMap q) (hg : Continuous g)
    (hf : ∀ x, q x = c → g x ∈ S → ContDiffAt ℝ 1 (combined q g) x)
    (hregular : ∀ x, q x = c → g x ∈ S → Function.Surjective (fderiv ℝ (combined q g) x))
    {A : Type*} [TopologicalSpace A] {base : A → S} {s d : A → Level q c}
    (hbase : Continuous base) (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ a, projection q g c (s a) = (base a).val)
    (hpd : ∀ a, projection q g c (d a) = (base a).val) :
    IsClopen {a | JoinedIn ((projection q g c) ⁻¹' {(base a).val}) (s a) (d a)} := by
  obtain ⟨chart, hsource, hfirst⟩ := exists_charts q g c S hf hregular
  have hsmem (a : A) : projection q g c (s a) ∈ S := by rw [hps]; exact (base a).property
  have hdmem (a : A) : projection q g c (d a) ∈ S := by rw [hpd]; exact (base a).property
  let s' : A → Slab q g c S := fun a => ⟨s a, hsmem a⟩
  let d' : A → Slab q g c S := fun a => ⟨d a, hdmem a⟩
  have hs' : Continuous s' := hs.subtype_mk _
  have hd' : Continuous d' := hd.subtype_mk _
  have hps' (a : A) : S.restrictPreimage (projection q g c) (s' a) = base a := Subtype.ext (hps a)
  have hpd' (a : A) : S.restrictPreimage (projection q g c) (d' a) = base a := Subtype.ext (hpd a)
  have h := LocalProductFibers.isClopen_joined_along (S.restrictPreimage (projection q g c))
    chart hsource hfirst ((isProperMap q g c hq hg).restrictPreimage S) hbase hs' hd' hps' hpd'
  have he : {a | JoinedIn ((S.restrictPreimage (projection q g c)) ⁻¹' {base a}) (s' a) (d' a)} =
      {a | JoinedIn ((projection q g c) ⁻¹' {(base a).val}) (s a) (d a)} := by
    ext a
    exact RegularComponentTransport.joinedIn_restrictPreimage_iff (projection q g c) S (base a)
      (s' a) (d' a) (hps' a) (hpd' a)
  rwa [he] at h

theorem joined_sections_iff (q g : E → ℝ) (c : ℝ) (S : Set ℝ) [PreconnectedSpace S]
    (hq : IsProperMap q) (hg : Continuous g)
    (hf : ∀ x, q x = c → g x ∈ S → ContDiffAt ℝ 1 (combined q g) x)
    (hregular : ∀ x, q x = c → g x ∈ S → Function.Surjective (fderiv ℝ (combined q g) x))
    {s d : S → Level q c} (hs : Continuous s) (hd : Continuous d)
    (hps : ∀ a, projection q g c (s a) = a.val) (hpd : ∀ a, projection q g c (d a) = a.val)
    (a b : S) :
    JoinedIn ((projection q g c) ⁻¹' {a.val}) (s a) (d a) ↔
      JoinedIn ((projection q g c) ⁻¹' {b.val}) (s b) (d b) := by
  have h := isClopen_joined_along q g c S hq hg hf hregular continuous_id hs hd hps hpd
  constructor
  · intro ha
    exact (isPreconnected_univ.subset_isClopen h ⟨a, mem_univ a, ha⟩) (mem_univ b)
  · intro hb
    exact (isPreconnected_univ.subset_isClopen h ⟨b, mem_univ b, hb⟩) (mem_univ a)

end LeanCanny.Geometry.HypersurfaceSweep
