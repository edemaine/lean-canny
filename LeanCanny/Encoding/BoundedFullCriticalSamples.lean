/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullDirectionChoice
public import LeanCanny.ETR.ComplexCriticalKernelRegular
public import LeanCanny.Encoding.RegularRootLabels
public import LeanCanny.Geometry.ComponentCriticalSampling

/-! # Finite critical samples of the constructed full source

The actual selected direction makes every real critical sample simple.
Concrete affine coordinate equations bound the number of samples by an
exponential in a natively computed polynomial label width. The sample family
uses the same integer source and direction as the circuit writers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullCriticalSamples
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Geometry LeanCanny.Algebra
open BoundedFullWriter MvPolynomial
open scoped Classical

noncomputable def polynomial (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c + 4)) ℤ :=
  BoundedFullGeometry.polynomial (original P c) (size P c) (size P c) (P.radius c)

noncomputable def direction (P : Readers) (c : List Bool) : ℕ → ℤ :=
  BoundedFullDirectionQueries.direction P (fun _ => BoundedFullDirectionChoice.record P c) c

noncomputable def equations (P : Readers) (c : List Bool) :=
  CriticalKernel.finiteRows (polynomial P c) (fun i => direction P c i.val)

abbrev Samples (P : Readers) (c : List Bool) := RegularAffineRootCount.Roots (equations P c)

noncomputable def labelWidth (P : Readers) (c : List Bool) : ℕ :=
  RegularAffineRootCount.labelWidth (P.dim c + 4) (degree P c)

theorem source_degree (P : Readers) (c : List Bool) : (polynomial P c).totalDegree ≤ degree P c := by
  unfold polynomial
  rw [BoundedFullGeometry.polynomial_eq]
  apply FermatCriticalHomogenization.polynomial_degree
  exact (totalDegree_rename_le _ _).trans_lt (IntegerRegularSource.lower_degree _ _ _
    (BoundedRegularSource.lower_degree _ _ _ _ (original_degree P c)))

theorem equations_degree (P : Readers) (c : List Bool) (j : Fin (P.dim c + 4)) :
    (equations P c j).totalDegree ≤ degree P c := by
  refine Fin.cases (source_degree P c) (fun j => ?_) j
  change (pderiv j.succ (polynomial P c) - C (direction P c j.val) * pderiv 0 (polynomial P c)).totalDegree ≤ degree P c
  have hp (i : Fin (P.dim c + 4)) : (pderiv i (polynomial P c)).totalDegree ≤ degree P c :=
    (PartialDerivativeDegree.degree_le _ _).trans ((Nat.sub_le _ _).trans (source_degree P c))
  apply (totalDegree_sub _ _).trans
  apply max_le (hp _)
  exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C, Nat.zero_add] using hp 0)

theorem regular (P : Readers) (c : List Bool) (x : Samples P c) :
    (fderiv ℝ (fun y => fun j => (equations P c j).eval₂ (Int.castRingHom ℝ) y) x.val).IsInvertible :=
  CriticalKernel.real_regular_of_no_bad (polynomial P c) (direction P c)
    (BoundedFullDirectionChoice.record_good P c) x.val x.property

theorem finite_samples (P : Readers) (c : List Bool) :
    Finite (Samples P c) ∧ Nat.card (Samples P c) ≤ 2 ^ labelWidth P c :=
  RegularAffineRootCount.finite_card_le_uniform (equations P c) (degree P c) (equations_degree P c)
    (by
      change 0 < BoundedZeroSource.powerDegree (size P c)
      have := BoundedRegularSource.powerDegree_gt_one (size P c)
      omega) (regular P c)

theorem labelWidth_unary {P : Readers} (h : P.PolyTime) : UnaryFn (labelWidth P) :=
  RegularRootLabels.width_unary (h.dim.add (UnaryFn.const 4)) (degree_binary h)

noncomputable def realPolynomial (P : Readers) (c : List Bool) : MvPolynomial (Fin (P.dim c + 4)) ℝ :=
  (polynomial P c).map (Int.castRingHom ℝ)

noncomputable def normalizedDirection (P : Readers) (c : List Bool) : Fin (P.dim c + 4) → ℝ :=
  Fin.cons 1 (fun j => (direction P c j.val : ℝ))

theorem equations_zero_iff (P : Readers) (c : List Bool) (x : Fin (P.dim c + 4) → ℝ) :
    (∀ j, (equations P c j).eval₂ (Int.castRingHom ℝ) x = 0) ↔
      (realPolynomial P c).eval x = 0 ∧ ∀ i,
        (pderiv i (realPolynomial P c)).eval x = normalizedDirection P c i *
          (pderiv 0 (realPolynomial P c)).eval x := by
  simp only [equations, CriticalKernel.finiteRows, realPolynomial, normalizedDirection,
    Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, eval₂_sub, eval₂_mul, eval₂_C,
    pderiv_map, eval_map, one_mul, sub_eq_zero, true_and]
  rfl

theorem source_regular (P : Readers) (c : List Bool) (x : Fin (P.dim c + 4) → ℝ)
    (hx : (realPolynomial P c).eval x = 0) :
    Function.Surjective (fderiv ℝ (fun y => (realPolynomial P c).eval y) x) := by
  apply RegularPolynomialLevels.surjective_of_ne_zero
  intro hzero
  have hx' : (polynomial P c).eval₂ (Int.castRingHom ℝ) x = 0 := by
    simpa only [realPolynomial, eval_map] using hx
  obtain ⟨j, hj⟩ := BoundedFullGeometry.generated_regular P c x hx'
  have hz : fderiv ℝ (fun y => (polynomial P c).eval₂ (Int.castRingHom ℝ) y) x = 0 := by
    simpa only [realPolynomial, eval_map] using hzero
  exact hj ((PolynomialCalculus.critical_iff (Int.castRingHom ℝ) (polynomial P c) x).mp hz j)

theorem source_proper (P : Readers) (c : List Bool) :
    IsProperMap (fun x => (realPolynomial P c).eval x) := by
  simpa only [realPolynomial, polynomial, eval_map] using
    BoundedFullGeometry.proper (original P c) (size P c) (size P c) (P.radius c)

/-- Every point reaches a sample inside its own source component. The
direction is the actual bounded-search output, rather than a new generic
choice made in the geometric proof. -/
theorem exists_joined_sample (P : Readers) (c : List Bool) (x : Fin (P.dim c + 4) → ℝ)
    (hx : (realPolynomial P c).eval x = 0) :
    ∃ y : Samples P c, JoinedIn {z | (realPolynomial P c).eval z = 0} x y.val := by
  have hv : normalizedDirection P c 0 = 1 := Fin.cons_zero _ _
  obtain ⟨y, hj, hy⟩ := ComponentCriticalSampling.exists_joined_critical (realPolynomial P c) 0
    (normalizedDirection P c) hv 0 ((source_proper P c).isCompact_preimage isCompact_singleton)
    (source_regular P c) x hx
  have hrows := (ProjectionCriticalBranches.value_iff (realPolynomial P c) 0
    (normalizedDirection P c) hv 0 y).mp hy
  exact ⟨⟨y, (equations_zero_iff P c y).mpr hrows⟩, hj⟩

abbrev Source (P : Readers) (c : List Bool) :=
  RegularFiber.Fiber (fun x => (realPolynomial P c).eval x) 0

noncomputable def samplePoint (P : Readers) (c : List Bool) (x : Samples P c) : Source P c :=
  ⟨x.val, ((equations_zero_iff P c x.val).mp x.property).1⟩

noncomputable def componentMap (P : Readers) (c : List Bool) : Samples P c → ConnectedComponents (Source P c) :=
  fun x => ConnectedComponents.mk (samplePoint P c x)

theorem componentMap_surjective (P : Readers) (c : List Bool) :
    Function.Surjective (componentMap P c) := by
  intro component
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe component
  obtain ⟨y, hj⟩ := exists_joined_sample P c x.val x.property
  refine ⟨y, ConnectedComponents.coe_eq_coe'.mpr ?_⟩
  exact pathComponent_subset_component x hj.joined_subtype

theorem finite_components (P : Readers) (c : List Bool) :
    Finite (ConnectedComponents (Source P c)) ∧
      Nat.card (ConnectedComponents (Source P c)) ≤ 2 ^ labelWidth P c := by
  let : Finite (Samples P c) := (finite_samples P c).1
  exact ⟨Finite.of_surjective _ (componentMap_surjective P c),
    (Nat.card_le_card_of_surjective _ (componentMap_surjective P c)).trans (finite_samples P c).2⟩

/-- All source components are represented, and each component is a path
component. Connectivity is therefore exactly pairwise connectivity of the
actual finite sample set; the empty source is accepted. -/
theorem preconnected_iff_samples (P : Readers) (c : List Bool) :
    IsPreconnected {x | (realPolynomial P c).eval x = 0} ↔
      ∀ i j : Samples P c, JoinedIn {x | (realPolynomial P c).eval x = 0} i.val j.val := by
  constructor
  · intro h i j
    let : LocallyPathConnectedSpace (Source P c) := RegularFiber.locallyPathConnected
      (fun x => (realPolynomial P c).eval x) 0
      (fun _ => ((ProjectionCritical.contDiff_eval (RingHom.id ℝ) (realPolynomial P c)).of_le le_top).contDiffAt)
      (fun x => source_regular P c x.val x.property)
    let : ConnectedSpace (Source P c) := isConnected_iff_connectedSpace.mp
      ⟨⟨i.val, (samplePoint P c i).property⟩, h⟩
    let : PathConnectedSpace (Source P c) := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
    exact (joinedIn_iff_joined (samplePoint P c i).property (samplePoint P c j).property).mpr
      (PathConnectedSpace.joined (samplePoint P c i) (samplePoint P c j))
  · intro h
    by_cases hn : Set.Nonempty {x | (realPolynomial P c).eval x = 0}
    · apply (isPathConnected_iff.mpr ⟨hn, ?_⟩).isConnected.isPreconnected
      intro x hx y hy
      obtain ⟨i, hi⟩ := exists_joined_sample P c x hx
      obtain ⟨j, hj⟩ := exists_joined_sample P c y hy
      exact (hi.trans (h i j)).trans hj.symm
    · rw [Set.not_nonempty_iff_eq_empty.mp hn]
      exact isPreconnected_empty

end LeanCanny.Encoding.BoundedFullCriticalSamples
