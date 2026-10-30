/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.AffineShiftArcs
public import LeanCanny.Connectivity.FiniteFiberSlab

/-! # Constructed finite connectivity graphs for singular affine-height slabs

Infinity exclusion gives finite original fibers at every parameter. Complete
arcs outside the explicit exceptional polynomial and singleton endpoint roots
therefore construct a finite incidence graph of the entire closed slab.
Both point paths and whole-slab connectedness agree with graph reachability.
No endpoint cover, finite-root oracle, or endpoint regularity is an input.
This is a geometric graph; native endpoint equality and recursive formula
covers remain to be constructed.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AffineShiftSlab
open Set Geometry LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def equation (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (t : ℝ) (x : Fin n → ℝ) : Prop := PolynomialGridValues.value (AffineShiftCoordinates.rows p c) (t, x) = 0

/-- Every vertex is an actual anchor or endpoint root, and every graph edge is
endpoint equality or vertex equality. Finite endpoint fibers are derived. -/
theorem exists_graph (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hdeg : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i)
    (hp : AffineFiniteCoordinates.NoInfinity p d) (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t
      (AffineShiftArcs.exceptional p c d) ≠ 0) :
    Finite (FiniteFiberSlab.Index (equation p c) (AffineShiftArcs.Fiber p c t₀.val) a b) ∧
    ∃ curve : AffineShiftArcs.Fiber p c t₀.val → ℝ → Fin n → ℝ,
      (∀ j, curve j t₀.val = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → equation p c t (curve j t)) ∧
      (∀ z : SlabCover.Space (equation p c) a b,
        ∃ i, z ∈ FiniteFiberSlab.piece (equation p c) curve a b i) ∧
      (∀ i, FrontierCover.Accessible (FiniteFiberSlab.piece (equation p c) curve a b i)) ∧
      (∀ i j, FrontierCover.Incident (FiniteFiberSlab.piece (equation p c) curve a b) i j ↔
        FiniteFiberSlab.Edge (equation p c) curve a b i j) ∧
      (∀ i j (x y : SlabCover.Space (equation p c) a b),
        x ∈ FiniteFiberSlab.piece (equation p c) curve a b i →
        y ∈ FiniteFiberSlab.piece (equation p c) curve a b j →
        (JoinedIn univ x y ↔ Relation.ReflTransGen (FiniteFiberSlab.Edge (equation p c) curve a b) i j)) ∧
      (IsPreconnected (univ : Set (SlabCover.Space (equation p c) a b)) ↔
        ∀ i j, Relation.ReflTransGen (FiniteFiberSlab.Edge (equation p c) curve a b) i j) := by
  have hf (t : ℝ) : Finite (AffineShiftArcs.Fiber p c t) :=
    (AffineShiftCoordinates.finite_fiber p c d hdeg hd hp t).to_subtype
  let : Finite (FiniteFiberSlab.Fiber (equation p c) a) := hf a
  let : Finite (FiniteFiberSlab.Fiber (equation p c) b) := hf b
  let : Finite (AffineShiftArcs.Fiber p c t₀.val) := hf t₀.val
  obtain ⟨_, curve, hanchor, hc, hroot, hcomplete, _⟩ := IntegerGridArcs.anchored_arcs
    (AffineShiftCoordinates.coordinate p c d) (AffineConstantParameterShift.system p c)
    (AffineShiftCoordinates.coordinate_degree_pos p c d hd hp) (AffineShiftCoordinates.proper p c d hd hp)
    (AffineShiftCoordinates.capture p c d hdeg) a b t₀ havoid
  have hroots : ∀ j t, t ∈ Icc a b → equation p c t (curve j t) := hroot
  have hcover (t : ℝ) (ht : t ∈ Ioo a b) (x : Fin n → ℝ) (hx : equation p c t x) :
      ∃ j, curve j t = x := by
    obtain ⟨j, hj, _⟩ := (hcomplete ⟨t, ht⟩ x).mp hx
    exact ⟨j, hj⟩
  have hinj (t : ℝ) (ht : t ∈ Ioo a b) : Function.Injective (fun j => curve j t) := by
    intro i j he
    obtain ⟨k, _, huniq⟩ := (hcomplete ⟨t, ht⟩ (curve i t)).mp (hroots i t (Ioo_subset_Icc_self ht))
    exact (huniq i rfl).trans (huniq j he.symm).symm
  have hab := t₀.property.1.trans t₀.property.2
  refine ⟨inferInstance, curve, hanchor, hc, hroots,
    FiniteFiberSlab.cover _ curve hcover, FiniteFiberSlab.accessible _ hab curve hc hroots,
    FiniteFiberSlab.incident_iff _ hab curve hc hroots hinj, ?_,
    FiniteFiberSlab.isPreconnected_iff_reachable _ hab curve hc hroots hcover hinj⟩
  intro i j x y hx hy
  exact FiniteFiberSlab.joinedIn_iff_reachable _ hab curve hc hroots hcover hinj hx hy

end LeanCanny.Connectivity.AffineShiftSlab
