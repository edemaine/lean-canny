/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.BitPathCover
public import LeanCanny.Connectivity.Problem
public import LeanCanny.ETR.CoercivePSPACE

/-! # Semialgebraic cover graphs via ETR

For a supplied cover by formula-defined pieces, nonemptiness and intersection
are ETR queries. Thus the existing ETR theorem supplies both graph routines;
there is no additional adjacency oracle assumption. The remaining effective
obligation is to construct a closed path cover with polynomial-width indices
and polynomial-time query writers. This module does not construct that cover.
-/

@[expose] public section

namespace LeanCanny.Connectivity
open ETR Computation Turing.MultiTapeTM
open scoped Classical

private theorem satisfiable_iff_tuple {p : Formula} {n : ℕ} (hp : p.arity ≤ n) :
    p.Satisfiable ↔ ∃ x : Fin n → ℝ, p.Holds (Formula.extend x) := by
  constructor
  · rintro ⟨env, h⟩
    refine ⟨fun i => env i.val, (p.holds_congr env _ ?_).mp h⟩
    intro i hi
    simp [Formula.extend, hi.trans_le hp]
  · rintro ⟨x, h⟩
    exact ⟨Formula.extend x, h⟩

/-- Any polynomial-time writer of encoded ETR queries has a polynomial-space
truth routine, charged for both query construction and ETR evaluation. -/
theorem satisfiable_computable {α : Type} {enc : α ↪ List Bool} {query : α → Formula}
    (hq : ComputableTidilyInPolyTime (fun a => (query a).encode) enc encBits) :
    ComputableTidilyInPolySpace (fun a => decide (query a).Satisfiable) enc encBool := by
  obtain ⟨f, hf, hL⟩ := NativeSpace.mem_iff.mp etr_mem_PSPACE
  apply (hf.comp (.of_polyTime hq)).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, ← hL, encode_mem_language]

/-- A piece as a subset of the described space, so closedness is relative. -/
def formulaPiece (d : Description) (p : Formula) : Set d.realization :=
  {x | p.Holds (Formula.extend x.val)}

/-- The query includes the ambient space formula; points outside the space
cannot create graph edges. -/
def nonemptyQuery (d : Description) (p : Formula) : Formula := .and d.formula p

def overlapQuery (d : Description) (p q : Formula) : Formula :=
  .and d.formula (.and p q)

theorem nonemptyQuery_correct {d : Description} (hd : d.WellFormed)
    {p : Formula} (hp : p.arity ≤ d.dimension) :
    (nonemptyQuery d p).Satisfiable ↔ (formulaPiece d p).Nonempty := by
  rw [satisfiable_iff_tuple (by exact max_le hd hp)]
  constructor
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨x, hx⟩, hp⟩
  · rintro ⟨x, hx⟩
    exact ⟨x.val, x.property, hx⟩

theorem overlapQuery_correct {d : Description} (hd : d.WellFormed)
    {p q : Formula} (hp : p.arity ≤ d.dimension) (hq : q.arity ≤ d.dimension) :
    (overlapQuery d p q).Satisfiable ↔ (formulaPiece d p ∩ formulaPiece d q).Nonempty := by
  rw [satisfiable_iff_tuple (by exact max_le hd (max_le hp hq))]
  constructor
  · rintro ⟨x, hx, hp, hq⟩
    exact ⟨⟨x, hx⟩, hp, hq⟩
  · rintro ⟨x, hp, hq⟩
    exact ⟨x.val, x.property, hp, hq⟩

/-- Geometric data only. Effectivity of the query writers is stated separately
and is not inferred from the existence of a mathematical cover. -/
structure FormulaPathCover (d : Description) (w : ℕ) where
  wellFormed : d.WellFormed
  formula : List Bool → Formula
  arity : ∀ u, u.length = w → (formula u).arity ≤ d.dimension
  closed : ∀ u, u.length = w → IsClosed (formulaPiece d (formula u))
  cover : ∀ x : d.realization, ∃ u, u.length = w ∧ x ∈ formulaPiece d (formula u)
  paths : ∀ u, u.length = w → ∀ x ∈ formulaPiece d (formula u),
    ∀ y ∈ formulaPiece d (formula u), JoinedIn (formulaPiece d (formula u)) x y

namespace FormulaPathCover
variable {d : Description} {w : ℕ} (C : FormulaPathCover d w)

noncomputable def valid (u : List Bool) : Bool :=
  decide (nonemptyQuery d (C.formula u)).Satisfiable

noncomputable def edge (u v : List Bool) : Bool :=
  decide (overlapQuery d (C.formula u) (C.formula v)).Satisfiable

/-- Test whether a piece contains the point described by an endpoint formula. -/
noncomputable def endpointTest (p : Formula) (u : List Bool) : Bool :=
  decide (overlapQuery d (C.formula u) p).Satisfiable

theorem endpointTest_correct {p : Formula} {x : d.realization}
    (hx : Denotes d.dimension p x.val) {u : List Bool} (hu : u.length = w) :
    C.endpointTest p u = true ↔ x ∈ formulaPiece d (C.formula u) := by
  rw [endpointTest, decide_eq_true_eq,
    overlapQuery_correct C.wellFormed (C.arity u hu) hx.1]
  constructor
  · rintro ⟨y, hy, hyp⟩
    have he : y = x := Subtype.ext ((hx.2 y.val).mp hyp)
    simpa only [he] using hy
  · intro h
    exact ⟨x, h, (hx.2 x.val).mpr rfl⟩

/-- ETR supplies exact nonemptiness and intersection tests for the cover. -/
noncomputable def toBitPathCover : BitPathCover d.realization w C.edge C.valid where
  piece i := formulaPiece d (C.formula i.val)
  closed i := C.closed i.val i.property
  cover x := by
    obtain ⟨u, hu, hx⟩ := C.cover x
    exact ⟨⟨u, hu⟩, hx⟩
  paths i := C.paths i.val i.property
  valid_iff i := by
    simp only [valid, decide_eq_true_eq]
    exact nonemptyQuery_correct C.wellFormed (C.arity i.val i.property)
  edge_iff i j := by
    simp only [edge, decide_eq_true_eq]
    exact overlapQuery_correct C.wellFormed (C.arity i.val i.property)
      (C.arity j.val j.property)

include C in
/-- On these covered spaces, topological connectivity and pairwise path
connectivity coincide. The empty space is included. -/
theorem connected_iff_pathConnected : d.Connected ↔ d.PathConnected := by
  refine ⟨fun h => ⟨h.1, ?_⟩, Description.PathConnected.connected⟩
  intro x hx y hy
  let a : d.realization := ⟨x, hx⟩
  let b : d.realization := ⟨y, hy⟩
  obtain ⟨i, hi⟩ := C.toBitPathCover.cover a
  obtain ⟨j, hj⟩ := C.toBitPathCover.cover b
  have ht : IsPreconnected (Set.univ : Set d.realization) := by
    rw [← preconnectedSpace_iff_univ, ← isPreconnected_iff_preconnectedSpace]
    exact h.2
  have hg := C.toBitPathCover.isPreconnected_iff_connected.mp ht
  have hr := hg i.val i.property j.val j.property
    ((C.toBitPathCover.valid_iff i).mpr ⟨a, hi⟩)
    ((C.toBitPathCover.valid_iff j).mpr ⟨b, hj⟩)
  have hp := (C.toBitPathCover.joinedIn_iff_reachable i.property j.property hi hj).mpr
    ⟨(C.toBitPathCover.valid_iff i).mpr ⟨a, hi⟩,
      (C.toBitPathCover.valid_iff j).mpr ⟨b, hj⟩, hr⟩
  exact (joinedIn_iff_joined hx hy).mpr (joinedIn_univ.mp hp)

section Effective
variable {α : Type} {enc : α ↪ List Bool} {spaces : α → Description} {width : α → ℕ}
  (covers : ∀ a, FormulaPathCover (spaces a) (width a))
  (hw : ComputableTidilyInPolyTime width enc encUnary)
  (hn : ComputableTidilyInPolyTime
    (fun p : α × List Bool => (nonemptyQuery (spaces p.1) ((covers p.1).formula p.2)).encode)
    (encPair enc encBits) encBits)
  (he : ComputableTidilyInPolyTime
    (fun p : α × List Bool × List Bool =>
      (overlapQuery (spaces p.1) ((covers p.1).formula p.2.1)
        ((covers p.1).formula p.2.2)).encode)
    (encPair enc (encPair encBits encBits)) encBits)

/-- Enumerate possible endpoint pieces, retaining only one polynomial-size
identifier. The endpoint itself is never approximated by a rational point. -/
noncomputable def locateEndpoint (endpoint : α → Formula) : α → List Bool :=
  ImplicitGraph.findWord
    (fun p : α × List Bool => (covers p.1).endpointTest (endpoint p.1) p.2) width

@[simp] theorem locateEndpoint_length (endpoint : α → Formula) (a : α) :
    (locateEndpoint covers endpoint a).length = width a := ImplicitGraph.findWord_length _ _ _

theorem locateEndpoint_correct {endpoint : α → Formula} {a : α}
    {x : (spaces a).realization} (hx : Denotes (spaces a).dimension (endpoint a) x.val) :
    x ∈ formulaPiece (spaces a) ((covers a).formula (locateEndpoint covers endpoint a)) := by
  apply ((covers a).endpointTest_correct hx (locateEndpoint_length covers endpoint a)).mp
  apply ImplicitGraph.findWord_correct
    (test := fun p : α × List Bool => (covers p.1).endpointTest (endpoint p.1) p.2)
    (width := width) (c := a)
  obtain ⟨u, hu, h⟩ := (covers a).cover x
  exact ⟨u, hu, ((covers a).endpointTest_correct hx hu).mpr h⟩

include hw in
theorem locateEndpoint_computable [Inhabited α] {endpoint : α → Formula}
    (hq : ComputableTidilyInPolyTime
      (fun p : α × List Bool =>
        (overlapQuery (spaces p.1) ((covers p.1).formula p.2) (endpoint p.1)).encode)
      (encPair enc encBits) encBits) :
    ComputableTidilyInPolySpace (locateEndpoint covers endpoint) enc encBits :=
  ImplicitGraph.findWord_computable (satisfiable_computable hq) hw

include hw hn he in
/-- Once the cover and its query writers are supplied, whole-space
connectivity is polynomial-space computable by the completed ETR theorem. -/
theorem connected_computable [Inhabited α] :
    ComputableTidilyInPolySpace (fun a => decide (spaces a).Connected) enc encBool := by
  have H := BitPathCover.connected_computable (fun a => (covers a).toBitPathCover)
    (satisfiable_computable he) (satisfiable_computable hn) hw
  apply H.congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Description.Connected, (covers a).wellFormed, true_and]
  rw [← preconnectedSpace_iff_univ, ← isPreconnected_iff_preconnectedSpace]

include hw hn he in
/-- Native class membership for a uniformly supplied effective cover family. -/
theorem connected_mem_PSPACE [Inhabited α] :
    {a | (spaces a).Connected} ∈ Cslib.Complexity.PSPACE enc :=
  NativeSpace.of_computable (connected_computable covers hw hn he) (fun _ => by simp)

include hw hn he in
/-- Endpoint pieces are supplied by polynomial-space identifiers. Their membership proofs
must be established by the geometric construction. -/
theorem joinedIn_computable {src dst : α → List Bool}
    (hs : ComputableTidilyInPolySpace src enc encBits)
    (hd : ComputableTidilyInPolySpace dst enc encBits)
    (hsrc : ∀ a, (src a).length = width a) (hdst : ∀ a, (dst a).length = width a)
    {x y : (a : α) → (spaces a).realization}
    (hx : ∀ a, x a ∈ formulaPiece (spaces a) ((covers a).formula (src a)))
    (hy : ∀ a, y a ∈ formulaPiece (spaces a) ((covers a).formula (dst a))) :
    ComputableTidilyInPolySpace
      (fun a => decide (JoinedIn (spaces a).realization (x a).val (y a).val)) enc encBool := by
  have H := BitPathCover.joinedIn_computable (fun a => (covers a).toBitPathCover)
    (satisfiable_computable he) (satisfiable_computable hn) hw hs hd hsrc hdst hx hy
  apply H.congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, joinedIn_univ]
  exact (joinedIn_iff_joined (x a).property (y a).property).symm

include hw hn he in
/-- Transfer to the specified point-query semantics, including unique endpoint
descriptions. Endpoint validation and piece attachment remain hypotheses. -/
theorem pointQuery_computable {src dst : α → List Bool}
    (hs : ComputableTidilyInPolySpace src enc encBits)
    (hd : ComputableTidilyInPolySpace dst enc encBits)
    (hsrc : ∀ a, (src a).length = width a) (hdst : ∀ a, (dst a).length = width a)
    {source target : α → Formula} {x y : (a : α) → (spaces a).realization}
    (hx : ∀ a, x a ∈ formulaPiece (spaces a) ((covers a).formula (src a)))
    (hy : ∀ a, y a ∈ formulaPiece (spaces a) ((covers a).formula (dst a)))
    (hsource : ∀ a, Denotes (spaces a).dimension (source a) (x a).val)
    (htarget : ∀ a, Denotes (spaces a).dimension (target a) (y a).val) :
    ComputableTidilyInPolySpace
      (fun a => decide (PointQuery.mk (spaces a) (source a) (target a)).Reachable)
      enc encBool := by
  apply (joinedIn_computable covers hw hn he hs hd hsrc hdst hx hy).congr
  intro a
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [PointQuery.reachable_iff (hsource a) (htarget a)]
  simp only [(covers a).wellFormed, true_and]

include hw hn he in
/-- ETR locates endpoint pieces automatically. Only valid singleton endpoint
descriptions and the effective geometric cover are supplied. -/
theorem pointQuery_computable_of_queryWriters [Inhabited α] {source target : α → Formula}
    (hs : ComputableTidilyInPolyTime
      (fun p : α × List Bool =>
        (overlapQuery (spaces p.1) ((covers p.1).formula p.2) (source p.1)).encode)
      (encPair enc encBits) encBits)
    (ht : ComputableTidilyInPolyTime
      (fun p : α × List Bool =>
        (overlapQuery (spaces p.1) ((covers p.1).formula p.2) (target p.1)).encode)
      (encPair enc encBits) encBits)
    {x y : (a : α) → (spaces a).realization}
    (hx : ∀ a, Denotes (spaces a).dimension (source a) (x a).val)
    (hy : ∀ a, Denotes (spaces a).dimension (target a) (y a).val) :
    ComputableTidilyInPolySpace
      (fun a => decide (PointQuery.mk (spaces a) (source a) (target a)).Reachable)
      enc encBool :=
  pointQuery_computable covers hw hn he
    (locateEndpoint_computable covers hw hs) (locateEndpoint_computable covers hw ht)
    (locateEndpoint_length covers source) (locateEndpoint_length covers target)
    (fun a => locateEndpoint_correct covers (hx a))
    (fun a => locateEndpoint_correct covers (hy a)) hx hy

end Effective
end FormulaPathCover
end LeanCanny.Connectivity
