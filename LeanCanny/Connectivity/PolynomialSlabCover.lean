/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FiberSectionLimit
public import LeanCanny.Geometry.ComponentCriticalSampling
public import LeanCanny.Geometry.RegularComponentTransport
public import LeanCanny.Geometry.RootBranches
public import LeanCanny.Connectivity.RegularRootArcs
public import LeanCanny.Connectivity.ComponentSlabCover

/-! # A complete finite cover of an original polynomial regular slab

Choose an integer projection direction and finitely many exceptional levels.
Between those levels, the actual spatial critical equations give complete
global branches. Each branch indexes the full fiber component it samples.
These pieces cover every point of the original slab, are clopen and path
connected, and overlap exactly when their indexing roots are connected in one
sample fiber. Thus the construction preserves the original slab's components.

This is a geometric construction. It still lacks effective branch descriptions,
polynomial input-size bounds, and the full recursion across critical slices
and arbitrary Boolean semialgebraic inputs.
-/

@[expose] public section

namespace LeanCanny.Connectivity.PolynomialSlabCover
open Set Geometry
open LeanCanny.Algebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Space (p : MvPolynomial ι ℝ) (a b : ℝ) := {x : ι → ℝ // p.eval x ∈ Ioo a b}

def projection (p : MvPolynomial ι ℝ) (a b : ℝ) : Space p a b → Ioo a b :=
  (Ioo a b).restrictPreimage (fun x => p.eval x)

noncomputable def system (p : MvPolynomial ι ℝ) (pivot : ι)
    (u : ProjectionFiniteSpecialization.DirectionIndex pivot → ℕ) : ℝ × (ι → ℝ) → ι → ℝ :=
  PolynomialRootFamily.value (ProjectionCriticalBranches.equation p pivot
    (ProjectionFiniteSpecialization.normalizedDirection pivot (fun i => (u i : ℝ))))

noncomputable abbrev Index (p : MvPolynomial ι ℝ) (pivot : ι)
    (u : ProjectionFiniteSpecialization.DirectionIndex pivot → ℕ) (a b : ℝ) (t₀ : Ioo a b) :=
  RootBranches.Index (system p pivot u) a b t₀

def SampleEdge (p : MvPolynomial ι ℝ) (pivot : ι)
    (u : ProjectionFiniteSpecialization.DirectionIndex pivot → ℕ) (a b : ℝ) (t₀ : Ioo a b)
    (i j : Index p pivot u a b t₀) : Prop :=
  JoinedIn {x | p.eval x = t₀.val} i.val.val.val.2 j.val.val.val.2

/-- The index type consists of actual critical roots at the sample parameter.
No finite cover, regularity oracle, or branch enumeration is assumed as input. -/
theorem exists_cover (p : MvPolynomial ι ℝ) (pivot : ι)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ u : ProjectionFiniteSpecialization.DirectionIndex pivot → ℕ,
      ∃ r : Polynomial ℝ, r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
        ∀ (a b : ℝ) (t₀ : Ioo a b), (∀ t ∈ Ioo a b, r.eval t ≠ 0) →
          Finite (Index p pivot u a b t₀) ∧
          ∃ arc : Index p pivot u a b t₀ → ℝ → ι → ℝ,
            (∀ j, ContinuousOn (arc j) (Icc a b)) ∧
            (∀ j t, t ∈ Icc a b → system p pivot u (t, arc j t) = 0) ∧
          ∃ sections : Index p pivot u a b t₀ → C(Ioo a b, Space p a b),
            (∀ j t, projection p a b (sections j t) = t) ∧
            (∀ j, (sections j t₀).val = j.val.val.val.2) ∧
            (∀ j t, (sections j t).val = arc j t.val) ∧
            let piece := FiberSectionCover.piece (projection p a b) sections
            (∀ j, IsClopen (piece j)) ∧ (∀ x, ∃ j, x ∈ piece j) ∧
            (∀ j, ∀ x ∈ piece j, ∀ y ∈ piece j, JoinedIn (piece j) x y) ∧
            (∀ j, IsConnected (closure (Subtype.val '' piece j) ∩
              {x | p.eval x = a})) ∧
            (∀ j, IsConnected (closure (Subtype.val '' piece j) ∩
              {x | p.eval x = b})) ∧
            (∀ i j, ClosedPathCover.Overlap piece i j ↔ SampleEdge p pivot u a b t₀ i j) ∧
            (∀ i j (x y : Space p a b), x ∈ piece i → y ∈ piece j →
              (JoinedIn univ x y ↔ Relation.ReflTransGen (SampleEdge p pivot u a b t₀) i j)) ∧
            (IsPreconnected (univ : Set (Space p a b)) ↔
              ∀ i j, Relation.ReflTransGen (SampleEdge p pivot u a b t₀) i j) := by
  classical
  obtain ⟨u, r, hr, _, Q, hQ, hnative⟩ :=
    ProjectionCriticalBranches.exists_regular_direction_coordinates p pivot
  obtain ⟨c, hc, hcm⟩ := CriticalValueAnnihilator.exists_annihilator p
  refine ⟨u, r * c, mul_ne_zero hr hc, Polynomial.finite_setOfPred_isRoot (mul_ne_zero hr hc), ?_⟩
  intro a b t₀ havoid
  have hfac (t : ℝ) (ht : t ∈ Ioo a b) : r.eval t ≠ 0 ∧ c.eval t ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [Polynomial.eval_mul] using havoid t ht)
  let : ContractibleSpace (Ioo a b) := (convex_Ioo a b).contractibleSpace ⟨t₀.val, t₀.property⟩
  let : LocallyPathConnectedSpace (Ioo a b) := isOpen_Ioo.locallyPathConnectedSpace
  let v := ProjectionFiniteSpecialization.normalizedDirection pivot (fun i => (u i : ℝ))
  have hv : v pivot = 1 := by simp [v, ProjectionFiniteSpecialization.normalizedDirection]
  let f := system p pivot u
  have hproper : IsProperMap (RootProjection.projection f) :=
    ProjectionCriticalBranches.isProperMap p pivot v hv hp
  have hf (z : RootProjection.Space f) (_ : RootProjection.projection f z ∈ Ioo a b) :
      ContDiffAt ℝ 1 f z.val := (PolynomialRootFamily.contDiff_value _ 1).contDiffAt
  have hJac (z : RootProjection.Space f) (hz : RootProjection.projection f z ∈ Ioo a b) :
      (fderiv ℝ f z.val ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible :=
    (PolynomialRootFamily.isInvertible_iff _ z.val).mpr
      (hnative z.val.1 z.val.2 (hfac z.val.1 hz).1 z.property).1
  let : Finite (Index p pivot u a b t₀) := RootBranches.finite_index f a b t₀ hproper hf hJac
  refine ⟨inferInstance, ?_⟩
  obtain ⟨arc, hanchorArc, hcArc, hrootArc, hcompleteArc, _⟩ :=
    RegularRootArcs.exists_anchored_arcs f a b t₀ (PolynomialRootFamily.contDiff_value _ 1).continuous
      hproper hf hJac Q hQ (fun z hz => (hnative z.val.1 z.val.2 (hfac _ hz).1 z.property).2)
  let curve : Index p pivot u a b t₀ → C(Ioo a b, ι → ℝ) := fun j =>
    ⟨fun t => arc j t.val, continuousOn_iff_continuous_domRestrict.mp ((hcArc j).mono Ioo_subset_Icc_self)⟩
  have hanchor (j : Index p pivot u a b t₀) : curve j t₀ = j.val.val.val.2 := hanchorArc j
  have hroots (j : Index p pivot u a b t₀) (t : Ioo a b) : f (t.val, curve j t) = 0 :=
    hrootArc j t.val (Ioo_subset_Icc_self t.property)
  have hcomplete (t : Ioo a b) (x : ι → ℝ) : f (t.val, x) = 0 ↔ ∃! j, curve j t = x :=
    hcompleteArc t x
  have hlevel (j : Index p pivot u a b t₀) (t : Ioo a b) : p.eval (curve j t) = t.val :=
    ((ProjectionCriticalBranches.value_iff p pivot v hv t.val (curve j t)).mp (hroots j t)).1
  have hmem (j : Index p pivot u a b t₀) (t : Ioo a b) : p.eval (curve j t) ∈ Ioo a b := by
    rw [hlevel]
    exact t.property
  let sections : Index p pivot u a b t₀ → C(Ioo a b, Space p a b) :=
    fun j => ⟨fun t => ⟨curve j t, hmem j t⟩, (curve j).continuous.subtype_mk _⟩
  have hproj (j : Index p pivot u a b t₀) (t : Ioo a b) :
      projection p a b (sections j t) = t := Subtype.ext (hlevel j t)
  have hanch (j : Index p pivot u a b t₀) : (sections j t₀).val = j.val.val.val.2 := hanchor j
  let g : (ι → ℝ) → ℝ := fun x => p.eval x
  have hsmooth : ContDiff ℝ 1 g := (ProjectionCritical.contDiff_eval (RingHom.id ℝ) p).of_le le_top
  have hregular (x : ι → ℝ) (hx : p.eval x ∈ Ioo a b) : Function.Surjective (fderiv ℝ g x) :=
    ComponentCriticalSampling.regular_level_of_annihilator p c hcm (p.eval x) (hfac _ hx).2 x rfl
  obtain ⟨chart, hsource, hfirst⟩ := RegularComponentTransport.exists_charts g (Ioo a b)
    (fun _ _ => hsmooth.contDiffAt) hregular
  have hprojproper : IsProperMap (projection p a b) := hp.restrictPreimage (Ioo a b)
  have hsample : ∀ x : Space p a b, ∃ j,
      JoinedIn ((projection p a b) ⁻¹' {projection p a b x}) x (sections j (projection p a b x)) := by
    intro x
    have hcompact : IsCompact {z : ι → ℝ | p.eval z = p.eval x.val} :=
      hp.isCompact_preimage isCompact_singleton
    have hreg (z : ι → ℝ) (hz : p.eval z = p.eval x.val) : Function.Surjective (fderiv ℝ g z) :=
      hregular z (by rw [hz]; exact x.property)
    obtain ⟨y, hjoined, hroot⟩ := ComponentCriticalSampling.exists_joined_critical p pivot v hv
      (p.eval x.val) hcompact hreg x.val rfl
    obtain ⟨j, hj, _⟩ := (hcomplete (projection p a b x) y).mp hroot
    refine ⟨j, (RegularComponentTransport.joinedIn_restrictPreimage_iff g (Ioo a b)
      (projection p a b x) x (sections j (projection p a b x)) rfl (hproj _ _)).mpr ?_⟩
    change JoinedIn {z | p.eval z = p.eval x.val} x.val (curve j (projection p a b x))
    rw [hj]
    exact hjoined
  have hedge (i j : Index p pivot u a b t₀) :
      FiberSectionCover.SampleEdge (projection p a b) sections t₀ i j =
        SampleEdge p pivot u a b t₀ i j := by
    apply propext
    change JoinedIn (((Ioo a b).restrictPreimage g) ⁻¹' {t₀}) (sections i t₀) (sections j t₀) ↔ _
    rw [RegularComponentTransport.joinedIn_restrictPreimage_iff g (Ioo a b) t₀
      (sections i t₀) (sections j t₀) (hproj _ _) (hproj _ _)]
    change JoinedIn {x | p.eval x = t₀.val} (sections i t₀).val (sections j t₀).val ↔ _
    rw [hanch, hanch]
    rfl
  have hedges : FiberSectionCover.SampleEdge (projection p a b) sections t₀ =
      SampleEdge p pivot u a b t₀ := funext (fun i => funext (hedge i))
  refine ⟨arc, hcArc, hrootArc, sections, hproj, hanch, (fun _ _ => rfl),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact FiberSectionCover.isClopen_piece (projection p a b) sections chart hsource hfirst hprojproper hproj
  · exact FiberSectionCover.cover (projection p a b) sections hsample
  · exact FiberSectionCover.paths (projection p a b) sections chart hsource hfirst hprojproper hproj
  · intro j
    exact FiberSectionCover.isConnected_ambient_endpoint g sections chart hsource hfirst hp hproj
      (t₀.property.1.trans t₀.property.2) j
  · intro j
    exact FiberSectionCover.isConnected_ambient_endpoint_right g sections chart hsource hfirst hp hproj
      (t₀.property.1.trans t₀.property.2) j
  · intro i j
    rw [FiberSectionCover.overlap_iff_sample (projection p a b) sections chart hsource hfirst
      hprojproper hproj t₀ i j, hedge]
  · intro i j x y hx hy
    rw [← hedges]
    exact FiberSectionCover.joinedIn_iff_sample_reachable (projection p a b) sections chart
      hsource hfirst hprojproper hproj hsample t₀ hx hy
  · rw [← hedges]
    exact FiberSectionCover.isPreconnected_iff_sample_reachable (projection p a b) sections chart
      hsource hfirst hprojproper hproj hsample t₀

/-- The original polynomial supplies every interior hypothesis of the
closed-slab composition theorem, including connected limits at singular ends. -/
theorem exists_interior_data (p : MvPolynomial ι ℝ) (pivot : ι)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ u : ProjectionFiniteSpecialization.DirectionIndex pivot → ℕ,
      ∃ r : Polynomial ℝ, r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
        ∀ (a b : ℝ) (t₀ : Ioo a b), (∀ t ∈ Ioo a b, r.eval t ≠ 0) →
          Finite (Index p pivot u a b t₀) ∧
          Nonempty (ComponentSlabCover.InteriorData (fun x => p.eval x) a b
            (Index p pivot u a b t₀)) := by
  obtain ⟨u, r, hr, hfinite, h⟩ := exists_cover p pivot hp
  refine ⟨u, r, hr, hfinite, ?_⟩
  intro a b t₀ havoid
  obtain ⟨hfin, arc, hc, hroot, sections, hproj, _, hmatch, hcl, hcover, hpaths, hl, hr, _⟩ :=
    h a b t₀ havoid
  let v := ProjectionFiniteSpecialization.normalizedDirection pivot (fun i => (u i : ℝ))
  have hv : v pivot = 1 := by simp [v, ProjectionFiniteSpecialization.normalizedDirection]
  have hlevel (j : Index p pivot u a b t₀) (t : ℝ) (ht : t ∈ Icc a b) :
      p.eval (arc j t) = t :=
    ((ProjectionCriticalBranches.value_iff p pivot v hv t (arc j t)).mp (hroot j t ht)).1
  refine ⟨hfin, ⟨{
    piece := FiberSectionCover.piece (projection p a b) sections
    closed := fun j => (hcl j).isClosed
    cover := hcover
    paths := hpaths
    arc := arc
    continuous_arc := hc
    arc_mem := ?_
    level_left := fun j => hlevel j a ⟨le_rfl, t₀.property.1.le.trans t₀.property.2.le⟩
    level_right := fun j => hlevel j b ⟨t₀.property.1.le.trans t₀.property.2.le, le_rfl⟩
    limit_left := fun j => (hl j).isPreconnected
    limit_right := fun j => (hr j).isPreconnected }⟩⟩
  intro j t
  exact ⟨sections j t, FiberSectionCover.section_mem_piece (projection p a b) sections hproj j t, hmatch j t⟩

/-- Recursive endpoint component covers now give a finite closed path cover
of the entire original closed polynomial slab, including its singular ends. -/
theorem exists_closed_cover {L R : Type} [Finite L] [Finite R]
    (p : MvPolynomial ι ℝ) (pivot : ι) (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ u : ProjectionFiniteSpecialization.DirectionIndex pivot → ℕ,
      ∃ r : Polynomial ℝ, r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
        ∀ (a b : ℝ) (t₀ : Ioo a b), (∀ t ∈ Ioo a b, r.eval t ≠ 0) →
          ∀ (_left : ClopenPathCover ((fun x => p.eval x) ⁻¹' {a}) L)
            (_right : ClopenPathCover ((fun x => p.eval x) ⁻¹' {b}) R),
          Finite (Index p pivot u a b t₀) ∧
          ∃ P : ComponentSlabCover.SelectedIndex (Index p pivot u a b t₀) L R →
              Set ((fun x => p.eval x) ⁻¹' Icc a b),
            (∀ i, IsClosed (P i)) ∧ (∀ x, ∃ i, x ∈ P i) ∧
            (∀ i, ∀ x ∈ P i, ∀ y ∈ P i, JoinedIn (P i) x y) ∧
            (∀ i j x y, x ∈ P i → y ∈ P j →
              (JoinedIn univ x y ↔ Relation.ReflTransGen (ClosedPathCover.Overlap P) i j)) ∧
            (IsPreconnected (univ : Set ((fun x => p.eval x) ⁻¹' Icc a b)) ↔
              ∀ i j, (P i).Nonempty → (P j).Nonempty →
                Relation.ReflTransGen (ClosedPathCover.Overlap P) i j) := by
  obtain ⟨u, r, hr, hfinite, h⟩ := exists_interior_data p pivot hp
  refine ⟨u, r, hr, hfinite, ?_⟩
  intro a b t₀ havoid left right
  obtain ⟨hfin, ⟨D⟩⟩ := h a b t₀ havoid
  let : Finite (Index p pivot u a b t₀) := hfin
  have hab := t₀.property.1.trans t₀.property.2
  obtain ⟨leftOf, rightOf, hselect⟩ := ComponentSlabCover.exists_selection D left right
  refine ⟨hfin, ComponentSlabCover.selectedPiece D left right leftOf rightOf,
    ComponentSlabCover.selected_closed D left right leftOf rightOf hp.continuous,
    ComponentSlabCover.selected_cover D left right leftOf rightOf hselect,
    ComponentSlabCover.selected_paths D left right leftOf rightOf hp.continuous hab t₀, ?_,
    ComponentSlabCover.selected_isPreconnected_iff_reachable D left right leftOf rightOf hselect
      hp.continuous hab t₀⟩
  intro i j x y hx hy
  exact ComponentSlabCover.selected_joinedIn_iff_reachable D left right leftOf rightOf hselect
    hp.continuous hab t₀ hx hy

end LeanCanny.Connectivity.PolynomialSlabCover
