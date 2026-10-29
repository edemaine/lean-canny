/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.NamedParentChildNext

/-! # Complete bounded names for regular children of actual named parents

Every regular original-block critical point over an actual named parent has
a unique actual child parameter. Its canonical name is accepted by the native
ancestry validator and has the derived length allowance. Regularity of other
parent fibers is not assumed.
-/

@[expose] public section
namespace LeanCanny.Encoding.NamedParentChildSamples
open LeanCanny.Algebra LeanCanny.Computation
open NamedParentChildSelection (Inputs generic)
open NamedParentChildNext (Root childRoot parentRoot word next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildQueries.roots RationalParentChildCoordinates.parameter
  RationalParentChildCoordinates.coordinate RationalParentChildParameters.decode

theorem complete (F : Inputs) (u : List Bool) (p : NamedRationalParents.Root F.parent u)
    (y : Fin (F.dim u) → ℝ)
    (hy : ∀ i, (RationalParentChildParameters.originalRows (generic F) u p.val i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (RationalParentChildParameters.originalRows (generic F) u p.val i).eval z) y).IsInvertible) :
    ∃! x : Root F u, RationalParentChildParameters.decode (generic F) u x.val = Fin.cons p.val y := by
  obtain ⟨eta, he, _⟩ := RationalParentChildParameters.sample_complete (generic F) u p.val
    (F.parent.root_zero u p.val p.property) (F.parent.defined u p.val p.property) y hy hr
  have hm : eta.val ∈ RationalParentChildQueries.roots (generic F) u :=
    (RationalParentChildQueries.mem_roots (generic F) u eta.val).mpr eta.property
  have hp : RationalParentChildParents.retained (generic F) u eta.val ∈ F.parent.roots u := by
    rw [RationalParentChildParents.retained_of_decode (generic F) u eta.val p.val y he]
    exact p.property
  refine ⟨⟨eta.val, hm, hp⟩, he, ?_⟩
  intro z hz
  apply Subtype.ext
  apply RationalParentChildCoordinates.parameter_roots_ext (generic F) u z.val eta.val
    ((RationalParentChildQueries.mem_roots (generic F) u z.val).mp z.property.1).1 eta.property.1
  intro i
  simpa only [RationalParentChildParameters.decode] using congrFun (hz.trans he.symm) i

theorem accepted_name (F : Inputs) (u : List Bool) (p : NamedRationalParents.Root F.parent u)
    (y : Fin (F.dim u) → ℝ)
    (hy : ∀ i, (RationalParentChildParameters.originalRows (generic F) u p.val i).eval y = 0)
    (hr : (fderiv ℝ (fun z => fun i => (RationalParentChildParameters.originalRows (generic F) u p.val i).eval z) y).IsInvertible) :
    ∃ x : Root F u, RationalParentChildParameters.decode (generic F) u x.val = Fin.cons p.val y ∧
      (word F u x).length ≤ NamedParentChildNext.width F u ∧
      pair u (word F u x) ∈ NamedRationalParents.language (next F) := by
  obtain ⟨x, hx, _⟩ := complete F u p y hy hr
  exact ⟨x, hx, NamedParentChildNext.word_length F u x, NamedRationalParents.descriptor_valid (next F) u x⟩

theorem sample_iff (F : Inputs) (u : List Bool) (p : NamedRationalParents.Root F.parent u)
    (y : Fin (F.dim u) → ℝ) :
    (∃ x : Root F u, RationalParentChildParameters.decode (generic F) u x.val = Fin.cons p.val y) ↔
      (∀ i, (RationalParentChildParameters.originalRows (generic F) u p.val i).eval y = 0) ∧
        (fderiv ℝ (fun z => fun i =>
          (RationalParentChildParameters.originalRows (generic F) u p.val i).eval z) y).IsInvertible := by
  constructor
  · rintro ⟨x, hx⟩
    apply (RationalParentChildParameters.sample_iff (generic F) u p.val
      (F.parent.root_zero u p.val p.property) (F.parent.defined u p.val p.property) y).mp
    exact ⟨⟨x.val, (RationalParentChildQueries.mem_roots (generic F) u x.val).mp x.property.1⟩, hx⟩
  · rintro ⟨hy, hr⟩
    exact (complete F u p y hy hr).exists

theorem sound (F : Inputs) (u : List Bool) (x : Root F u) :
    let t := (parentRoot F u x).val
    let y := RationalParentChildParents.spatialPoint (generic F) u x.val
    (∀ i, (RationalParentChildParameters.originalRows (generic F) u t i).eval y = 0) ∧
      (fderiv ℝ (fun z => fun i =>
        (RationalParentChildParameters.originalRows (generic F) u t i).eval z) y).IsInvertible := by
  apply (sample_iff F u (parentRoot F u x) _).mp
  refine ⟨x, ?_⟩
  funext i
  refine Fin.cases ?_ (fun _ => rfl) i
  simp only [Fin.cons_zero, parentRoot, RationalParentChildParents.retained,
    RationalParentChildParents.first]
  apply congrArg (RationalParentChildParameters.decode (generic F) u x.val)
  exact Fin.ext rfl

theorem finite_roots (F : Inputs) (u : List Bool) : Finite (Root F u) :=
  Finite.of_injective (childRoot F u) (fun _ _ he => Subtype.ext
    (congrArg (fun z : RationalParentChildRecordSpan.Root (generic F) u => z.val) he))

theorem card_le (F : Inputs) (u : List Bool) :
    Nat.card (Root F u) ≤ RationalParentChildRegularCount.count (generic F) u := by
  have H := Nat.card_le_card_of_injective (childRoot F u)
    (fun _ _ he => Subtype.ext
      (congrArg (fun z : RationalParentChildRecordSpan.Root (generic F) u => z.val) he))
  simpa only [RationalParentChildRecordSpan.Root, RationalParentChildThom.Root,
    Nat.card_eq_fintype_card, Fintype.card_coe, RationalParentChildQueries.roots_card] using H

end LeanCanny.Encoding.NamedParentChildSamples
