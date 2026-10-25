/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CoordinateCriticalArcs
public import LeanCanny.Connectivity.FiberSectionLimit
public import LeanCanny.Connectivity.ComponentSlabCover

/-! # Component covers for a coordinate slab of a fixed hypersurface

The constructed critical arcs sample every component in every regular slice.
Saturating them produces a complete clopen path cover of the original sweep
slab, whose overlap tests are paths in a polynomial slice in one fewer
coordinate. Connected endpoint limits and continuous critical arcs supply the
closed-slab composition data, even at exceptional endpoints.
-/

@[expose] public section

namespace LeanCanny.Connectivity.CoordinateSlabCover
open Set Geometry
open LeanCanny.Algebra
open ProjectionFiniteSpecialization
set_option backward.isDefEq.respectTransparency false

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Level (p : MvPolynomial ι ℝ) (c : ℝ) := HypersurfaceSweep.Level (fun x => p.eval x) c

def sweep (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ) : Level p c → ℝ := fun x => x.val base

noncomputable abbrev Index (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base) (u : DirectionIndex pivot → ℕ)
    (a b : ℝ) (t₀ : Ioo a b) :=
  RootBranches.Index (CoordinateCriticalArcs.system p base c pivot u) a b t₀

def SampleEdge (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base) (u : DirectionIndex pivot → ℕ)
    (a b : ℝ) (t₀ : Ioo a b) (i j : Index p base c pivot u a b t₀) : Prop :=
  JoinedIn {x : CoordinateSlice.Index base → ℝ |
    (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t₀.val) x = 0}
      i.val.val.val.2 j.val.val.val.2

/-- Endpoint covers can be supplied by recursion on the actual slice equation,
including singular slices and irrational coordinates. -/
noncomputable def sliceHomeomorph (p : MvPolynomial ι ℝ) (base : ι) (c t : ℝ) :
    (sweep p base c ⁻¹' {t}) ≃ₜ {z : CoordinateSlice.Index base → ℝ |
      (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t) z = 0} := by
  let e : (sweep p base c ⁻¹' {t}) ≃ₜ {z : CoordinateSlice.Index base → ℝ |
      (CoordinateSlice.family base p).eval₂ (Polynomial.eval₂RingHom (RingHom.id ℝ) t) z = c} := by
    convert CoordinateSlice.fiberHomeomorph p (RingHom.id ℝ) base c t using 1
    rfl
  apply e.trans (Homeomorph.setCongr ?_)
  ext z
  change (CoordinateSlice.family base p).eval₂ (Polynomial.eval₂RingHom (RingHom.id ℝ) t) z = c ↔
    (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t) z = 0
  rw [CoordinateCriticalArcs.eval_equation, sub_eq_zero,
    CoordinateSlice.eval_family base p (RingHom.id ℝ) t z, MvPolynomial.eval₂_id]

/-- Every cover and branch comes from the polynomial equations. The graph
edge is a connection test in one actual lower-dimensional polynomial slice. -/
theorem exists_interior_data (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (pivot : CoordinateSlice.Index base)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x))
    (hregular : ∀ x : ι → ℝ, p.eval x = c →
      Function.Surjective (fderiv ℝ (fun y => p.eval y) x)) :
    ∃ u : DirectionIndex pivot → ℕ, ∃ r : Polynomial ℝ,
      r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
      ∀ (a b : ℝ) (t₀ : Ioo a b), (∀ t ∈ Ioo a b, r.eval t ≠ 0) →
        Finite (Index p base c pivot u a b t₀) ∧
        ∃ D : ComponentSlabCover.InteriorData (sweep p base c) a b
            (Index p base c pivot u a b t₀),
          (∀ j, IsClopen (D.piece j)) ∧
          (∀ i j, ClosedPathCover.Overlap D.piece i j ↔
            SampleEdge p base c pivot u a b t₀ i j) ∧
          ∀ i j x y, x ∈ D.piece i → y ∈ D.piece j →
            (JoinedIn univ x y ↔ Relation.ReflTransGen
              (SampleEdge p base c pivot u a b t₀) i j) := by
  classical
  obtain ⟨u, r, hr, _, harcs⟩ := CoordinateCriticalArcs.exists_arcs p base c pivot hp hregular
  obtain ⟨d, hd, _, hcombined⟩ := PolynomialHypersurfaceSweep.exists_exceptional p base c hregular
  refine ⟨u, r * d, mul_ne_zero hr hd,
    Polynomial.finite_setOfPred_isRoot (mul_ne_zero hr hd), ?_⟩
  intro a b t₀ havoid
  have hab : a < b := t₀.property.1.trans t₀.property.2
  have hfac (t : ℝ) (ht : t ∈ Ioo a b) : r.eval t ≠ 0 ∧ d.eval t ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [Polynomial.eval_mul] using havoid t ht)
  obtain ⟨hfin, arc, hanchor, hc, hroot, hcomplete, hlevel⟩ :=
    harcs a b t₀ (fun t ht => (hfac t ht).1)
  let J := Index p base c pivot u a b t₀
  let : Finite J := hfin
  let : ContractibleSpace (Ioo a b) := (convex_Ioo a b).contractibleSpace ⟨t₀.val, t₀.property⟩
  let : LocallyPathConnectedSpace (Ioo a b) := isOpen_Ioo.locallyPathConnectedSpace
  let g := sweep p base c
  let projection := (Ioo a b).restrictPreimage g
  let restored : J → ℝ → ι → ℝ := fun j t => CoordinateSlice.restore base t (arc j t)
  let curve : J → ℝ → Level p c := fun j t =>
    if ht : t ∈ Icc a b then ⟨restored j t, hlevel j t ht⟩
    else ⟨restored j t₀.val, hlevel j t₀.val (Ioo_subset_Icc_self t₀.property)⟩
  have hcurve (j : J) (t : ℝ) (ht : t ∈ Icc a b) : (curve j t).val = restored j t := by
    simp only [curve, dite_eq_left ht]
  have hcCurve (j : J) : ContinuousOn (curve j) (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.congr
      ((continuousOn_iff_continuous_domRestrict.mp
        (CoordinateCriticalArcs.continuousOn_restore_curve base (hc j))).subtype_mk
          (fun t : Icc a b => hlevel j t.val t.property))
    intro t
    apply Subtype.ext
    exact (hcurve j t.val t.property).symm
  have hcoordinate (j : J) (t : ℝ) (ht : t ∈ Icc a b) : g (curve j t) = t := by
    change (curve j t).val base = t
    rw [hcurve j t ht]
    exact CoordinateSlice.restore_base base t (arc j t)
  let sections : J → C(Ioo a b, g ⁻¹' Ioo a b) := fun j =>
    ⟨fun t => ⟨curve j t.val, by
      change g (curve j t.val) ∈ Ioo a b
      rw [hcoordinate j t.val (Ioo_subset_Icc_self t.property)]
      exact t.property⟩,
      (continuousOn_iff_continuous_domRestrict.mp ((hcCurve j).mono Ioo_subset_Icc_self)).subtype_mk
        (fun t => by
          change g (curve j t.val) ∈ Ioo a b
          rw [hcoordinate j t.val (Ioo_subset_Icc_self t.property)]
          exact t.property)⟩
  have hproj (j : J) (t : Ioo a b) : projection (sections j t) = t :=
    Subtype.ext (hcoordinate j t.val (Ioo_subset_Icc_self t.property))
  have hrest (j : J) (t : Ioo a b) : (sections j t).val.val = restored j t.val :=
    hcurve j t.val (Ioo_subset_Icc_self t.property)
  have hcoords (j : J) (t : Ioo a b) :
      (fun k : CoordinateSlice.Index base => (sections j t).val.val k.val) = arc j t.val := by
    funext k
    rw [hrest]
    exact CoordinateSlice.restore_other base t.val (arc j t.val) k
  have hgproper : IsProperMap g :=
    HypersurfaceSweep.isProperMap _ _ c hp (continuous_apply base)
  have hprojproper : IsProperMap projection := hgproper.restrictPreimage (Ioo a b)
  obtain ⟨chart, hsource, hfirst⟩ := HypersurfaceSweep.exists_charts
    (fun x => p.eval x) (fun x => x base) c (Ioo a b)
    (fun _ _ _ => ((ProjectionCritical.contDiff_eval (RingHom.id ℝ) p).prodMk
      (contDiff_apply ℝ (fun _ : ι => ℝ) base)).of_le le_top |>.contDiffAt)
    (fun x hx ht => hcombined x hx (hfac _ ht).2)
  have heqSlice (t : ℝ) :
      {z : CoordinateSlice.Index base → ℝ |
        (CoordinateSlice.family base p).eval₂ (Polynomial.eval₂RingHom (RingHom.id ℝ) t) z = c} =
      {z | (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t) z = 0} := by
    ext z
    change (CoordinateSlice.family base p).eval₂ (Polynomial.eval₂RingHom (RingHom.id ℝ) t) z = c ↔
      (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t) z = 0
    rw [CoordinateCriticalArcs.eval_equation, sub_eq_zero]
    have he := CoordinateSlice.eval_family base p (RingHom.id ℝ) t z
    rw [he, MvPolynomial.eval₂_id]
  have hsample : ∀ x : g ⁻¹' Ioo a b, ∃ j,
      JoinedIn (projection ⁻¹' {projection x}) x (sections j (projection x)) := by
    intro x
    let t := g x.val
    let rest : CoordinateSlice.Index base → ℝ := fun k => x.val.val k.val
    have hrestore : CoordinateSlice.restore base t rest = x.val.val :=
      CoordinateSlice.restore_coordinates base t x.val.val rfl
    have hx : (CoordinateCriticalArcs.equation p base c).eval₂ (Polynomial.evalRingHom t) rest = 0 := by
      have hxlevel : p.eval x.val.val = c := x.val.property
      rw [CoordinateCriticalArcs.eval_equation, hrestore, hxlevel, sub_self]
    obtain ⟨y, hj, hy⟩ := ParameterizedCriticalBranches.exists_joined_critical
      (CoordinateCriticalArcs.equation p base c) pivot u t
      (CoordinateCriticalArcs.isCompact_slice p base c t hp)
      (fun z hz => CoordinateCriticalArcs.slice_regular p base c t z
        (hcombined _ (by rwa [CoordinateCriticalArcs.eval_equation, sub_eq_zero] at hz)
          (by simpa only [CoordinateSlice.restore_base] using (hfac t x.property).2))) rest hx
    obtain ⟨j, hjroot, _⟩ := (hcomplete (projection x) y).mp hy
    refine ⟨j, (RegularComponentTransport.joinedIn_restrictPreimage_iff g (Ioo a b)
      (projection x) x (sections j (projection x)) rfl (hproj _ _)).mpr ?_⟩
    have hslice := CoordinateSlice.joinedIn_fiber_iff p (RingHom.id ℝ) base c t
      x.val (sections j (projection x)).val rfl (congrArg Subtype.val (hproj j (projection x)))
    simp only [MvPolynomial.eval₂_id] at hslice
    apply hslice.mpr
    rw [heqSlice, hcoords, hjroot]
    exact hj
  have hedge (i j : J) : FiberSectionCover.SampleEdge projection sections t₀ i j ↔
      SampleEdge p base c pivot u a b t₀ i j := by
    rw [FiberSectionCover.SampleEdge,
      RegularComponentTransport.joinedIn_restrictPreimage_iff g (Ioo a b) t₀
        (sections i t₀) (sections j t₀) (hproj _ _) (hproj _ _)]
    have hslice := CoordinateSlice.joinedIn_fiber_iff p (RingHom.id ℝ) base c t₀.val
      (sections i t₀).val (sections j t₀).val
        (congrArg Subtype.val (hproj i t₀)) (congrArg Subtype.val (hproj j t₀))
    simp only [MvPolynomial.eval₂_id] at hslice
    change JoinedIn (g ⁻¹' {t₀.val}) (sections i t₀).val (sections j t₀).val ↔ _ at hslice
    rw [hslice, heqSlice, hcoords, hcoords, hanchor, hanchor]
    rfl
  let D : ComponentSlabCover.InteriorData g a b J := {
    piece := FiberSectionCover.piece projection sections
    closed := fun j => (FiberSectionCover.isClopen_piece projection sections chart hsource hfirst
      hprojproper hproj j).isClosed
    cover := FiberSectionCover.cover projection sections hsample
    paths := FiberSectionCover.paths projection sections chart hsource hfirst hprojproper hproj
    arc := curve
    continuous_arc := hcCurve
    arc_mem := fun j t => ⟨sections j t,
      FiberSectionCover.section_mem_piece projection sections hproj j t, rfl⟩
    level_left := fun j => hcoordinate j a ⟨le_rfl, hab.le⟩
    level_right := fun j => hcoordinate j b ⟨hab.le, le_rfl⟩
    limit_left := fun j => (FiberSectionCover.isConnected_ambient_endpoint g sections chart hsource hfirst
      hgproper hproj hab j).isPreconnected
    limit_right := fun j => (FiberSectionCover.isConnected_ambient_endpoint_right g sections chart hsource hfirst
      hgproper hproj hab j).isPreconnected }
  refine ⟨hfin, D, ?_, ?_, ?_⟩
  · exact FiberSectionCover.isClopen_piece projection sections chart hsource hfirst hprojproper hproj
  · intro i j
    exact (FiberSectionCover.overlap_iff_sample projection sections chart hsource hfirst
      hprojproper hproj t₀ i j).trans (hedge i j)
  · intro i j x y hx hy
    have hedges : FiberSectionCover.SampleEdge projection sections t₀ =
        SampleEdge p base c pivot u a b t₀ := funext fun i => funext fun j => propext (hedge i j)
    rw [← hedges]
    exact FiberSectionCover.joinedIn_iff_sample_reachable projection sections chart hsource hfirst
      hprojproper hproj hsample t₀ hx hy

/-- Recursive endpoint covers complete the original closed coordinate slab.
The final label family is a sum, retaining the additive recursion size. -/
theorem exists_closed_cover {L R : Type} [Finite L] [Finite R]
    (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ) (pivot : CoordinateSlice.Index base)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x))
    (hregular : ∀ x : ι → ℝ, p.eval x = c →
      Function.Surjective (fderiv ℝ (fun y => p.eval y) x)) :
    ∃ u : DirectionIndex pivot → ℕ, ∃ r : Polynomial ℝ,
      r ≠ 0 ∧ {t : ℝ | r.eval t = 0}.Finite ∧
      ∀ (a b : ℝ) (t₀ : Ioo a b), (∀ t ∈ Ioo a b, r.eval t ≠ 0) →
        ∀ (_left : ClopenPathCover (sweep p base c ⁻¹' {a}) L)
          (_right : ClopenPathCover (sweep p base c ⁻¹' {b}) R),
        Finite (Index p base c pivot u a b t₀) ∧
        ∃ P : ComponentSlabCover.SelectedIndex (Index p base c pivot u a b t₀) L R →
            Set (sweep p base c ⁻¹' Icc a b),
          (∀ i, IsClosed (P i)) ∧ (∀ x, ∃ i, x ∈ P i) ∧
          (∀ i, ∀ x ∈ P i, ∀ y ∈ P i, JoinedIn (P i) x y) ∧
          (∀ i j x y, x ∈ P i → y ∈ P j →
            (JoinedIn univ x y ↔ Relation.ReflTransGen (ClosedPathCover.Overlap P) i j)) ∧
          (IsPreconnected (univ : Set (sweep p base c ⁻¹' Icc a b)) ↔
            ∀ i j, (P i).Nonempty → (P j).Nonempty →
              Relation.ReflTransGen (ClosedPathCover.Overlap P) i j) := by
  obtain ⟨u, r, hr, hfinite, h⟩ := exists_interior_data p base c pivot hp hregular
  refine ⟨u, r, hr, hfinite, ?_⟩
  intro a b t₀ havoid left right
  obtain ⟨hfin, D, _⟩ := h a b t₀ havoid
  let : Finite (Index p base c pivot u a b t₀) := hfin
  have hg : Continuous (sweep p base c) := (continuous_apply base).comp continuous_subtype_val
  have hab := t₀.property.1.trans t₀.property.2
  obtain ⟨leftOf, rightOf, hselect⟩ := ComponentSlabCover.exists_selection D left right
  refine ⟨hfin, ComponentSlabCover.selectedPiece D left right leftOf rightOf,
    ComponentSlabCover.selected_closed D left right leftOf rightOf hg,
    ComponentSlabCover.selected_cover D left right leftOf rightOf hselect,
    ComponentSlabCover.selected_paths D left right leftOf rightOf hg hab t₀, ?_,
    ComponentSlabCover.selected_isPreconnected_iff_reachable D left right leftOf rightOf hselect
      hg hab t₀⟩
  intro i j x y hx hy
  exact ComponentSlabCover.selected_joinedIn_iff_reachable D left right leftOf rightOf hselect
    hg hab t₀ hx hy

end LeanCanny.Connectivity.CoordinateSlabCover
