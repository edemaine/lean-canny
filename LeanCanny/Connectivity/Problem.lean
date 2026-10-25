/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Syntax
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Semialgebraic connectivity problems

The dimension is part of the input. A space is given by a Boolean combination
of integer polynomial sign conditions. Endpoints are described by formulas
whose solution sets must be singletons; this permits irrational algebraic
points without arbitrary real constants or a rational-sampling assumption.

Whole-space connectivity means `IsPreconnected`, accepting the empty set.
Pairwise path connectivity is stated separately: their equivalence for these
sets needs a geometric theorem and is not assumed here.
-/

@[expose] public section

namespace LeanCanny.Connectivity
open ETR

structure Description where
  dimension : ℕ
  formula : Formula
  deriving DecidableEq, Repr

namespace Description

def WellFormed (d : Description) : Prop := d.formula.arity ≤ d.dimension

def realization (d : Description) : Set (Fin d.dimension → ℝ) :=
  {x | d.formula.Holds (Formula.extend x)}

/-- Empty spaces are connected by the convention used in this development. -/
def Connected (d : Description) : Prop := d.WellFormed ∧ IsPreconnected d.realization

/-- The pairwise path version also accepts the empty space. -/
def PathConnected (d : Description) : Prop :=
  d.WellFormed ∧ ∀ x ∈ d.realization, ∀ y ∈ d.realization, JoinedIn d.realization x y

theorem PathConnected.connected {d : Description} (h : d.PathConnected) : d.Connected := by
  refine ⟨h.1, ?_⟩
  by_cases hne : d.realization.Nonempty
  · exact (isPathConnected_iff.mpr ⟨hne, h.2⟩).isConnected.isPreconnected
  · have he : d.realization = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    exact isPreconnected_empty

end Description

/-- A well-formed formula denotes exactly one point of the specified dimension.
Inconsistent and nonunique endpoint formulas are rejected. -/
def Denotes (n : ℕ) (p : Formula) (x : Fin n → ℝ) : Prop :=
  p.arity ≤ n ∧ ∀ y : Fin n → ℝ, p.Holds (Formula.extend y) ↔ y = x

theorem Denotes.unique {n : ℕ} {p : Formula} {x y : Fin n → ℝ}
    (hx : Denotes n p x) (hy : Denotes n p y) : x = y :=
  (hy.2 x).mp ((hx.2 x).mpr rfl)

structure PointQuery where
  space : Description
  source : Formula
  target : Formula
  deriving DecidableEq, Repr

namespace PointQuery

/-- Both described endpoints must lie in the space, as enforced by `JoinedIn`. -/
def Reachable (q : PointQuery) : Prop :=
  q.space.WellFormed ∧ ∃ x y : Fin q.space.dimension → ℝ,
    Denotes q.space.dimension q.source x ∧ Denotes q.space.dimension q.target y ∧
      JoinedIn q.space.realization x y

theorem reachable_iff {q : PointQuery} {x y : Fin q.space.dimension → ℝ}
    (hx : Denotes q.space.dimension q.source x) (hy : Denotes q.space.dimension q.target y) :
    q.Reachable ↔ q.space.WellFormed ∧ JoinedIn q.space.realization x y := by
  constructor
  · rintro ⟨hw, a, b, ha, hb, hab⟩
    exact ⟨hw, ha.unique hx ▸ hb.unique hy ▸ hab⟩
  · rintro ⟨hw, h⟩
    exact ⟨hw, x, y, hx, hy, h⟩

theorem Reachable.symm {q : PointQuery} (h : q.Reachable) :
    ({q with source := q.target, target := q.source} : PointQuery).Reachable := by
  obtain ⟨hw, x, y, hx, hy, hxy⟩ := h
  exact ⟨hw, y, x, hy, hx, hxy.symm⟩

end PointQuery
end LeanCanny.Connectivity
