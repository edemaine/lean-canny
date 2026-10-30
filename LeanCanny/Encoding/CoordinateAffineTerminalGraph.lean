/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CoordinateAffineTerminalReachability

/-! # Native complete-child graphs for terminal coordinate slices -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateAffineTerminalGraph
open LeanCanny.Algebra LeanCanny.Computation Turing.MultiTapeTM
open LeanCanny.Connectivity.CoordinateAffineTerminalReachability (childQuery)
open CoordinateAffinePrefix (inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def valid (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q w : List Bool) : Bool :=
  decide (FlatAffineSliceRegularity.query (pair q w) ∈ FlatAffineCompleteChildLabels.language
    (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level))

noncomputable def edge (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q w z : List Bool) : Bool :=
  decide (pair q (pair w z) ∈ LeanCanny.Connectivity.CoordinateAffineTerminalReachability.language P depth objective level)

theorem valid_packet (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u v w : List Bool) :
    valid P depth objective level (pair u v) w = true ↔
      pair u (pair w v) ∈ FlatAffineCompleteChildLabels.language (inputs P depth objective level)
        (CoordinateAffineSliceRegularity.cone P depth objective level) := by
  simp only [valid, FlatAffineSliceRegularity.query_packet, decide_eq_true_eq]

theorem edge_valid (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (q w z : List Bool) (he : edge P depth objective level q w z = true) :
    valid P depth objective level q w = true ∧ valid P depth objective level q z = true := by
  have H := of_decide_eq_true he
  change LeanCanny.Connectivity.CoordinateAffineTerminalReachability.terminal P depth objective (pair q (pair w z)) ∧ _ at H
  have HV := And.intro H.2.1 H.2.2.1
  simpa only [valid, decide_eq_true_eq, childQuery, LeanCanny.Connectivity.CoordinateAffineTerminalReachability.source,
    LeanCanny.Connectivity.CoordinateAffineTerminalReachability.word, LeanCanny.Connectivity.CoordinateAffineTerminalReachability.parent,
    FlatAffineSliceRegularity.query, pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true] using HV

theorem valid_computable {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ComputableTidilyInPolySpace (fun p : List Bool × List Bool => valid P depth objective level p.1 p.2)
      (encPair encBits encBits) encBool := by
  have D := (FlatAffineCompleteChildLabels.decider (CoordinateAffinePrefix.access hP hd ho hl hA)
    (CoordinateAffineSliceRegularity.cone P depth objective level)).precompose FlatAffineSliceRegularity.query FlatAffineSliceRegularity.query_FP
  exact D.computable.comp (.of_polyTime (pair_computable
    (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)))

theorem edge_computable {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    ComputableTidilyInPolySpace (fun p : List Bool × List Bool × List Bool => edge P depth objective level p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  have C := ComputableTidilyInPolyTime.fst encBits (encPair encBits encBits)
  have R := ComputableTidilyInPolyTime.snd encBits (encPair encBits encBits)
  exact (LeanCanny.Connectivity.CoordinateAffineTerminalReachability.decider hP hd ho hl hA).computable.comp
    (.of_polyTime (pair_computable C (pair_computable R.fst' R.snd')))

noncomputable def width (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ) (level : List Bool → List Bool) :=
  FlatAffineSliceRegularity.width (inputs P depth objective level) (CoordinateAffineSliceRegularity.cone P depth objective level)

theorem width_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : UnaryFn (width P depth objective level) :=
  FlatAffineSliceRegularity.width_unary (CoordinateAffinePrefix.access hP hd ho hl hA) (CoordinateAffineSliceRegularity.cone P depth objective level)

noncomputable def connectedLanguage (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  {q | ImplicitGraph.Connected (edge P depth objective level q) (valid P depth objective level q) (width P depth objective level q)}

theorem connectedDecider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth objective : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn objective) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) : SpaceDecider (connectedLanguage P depth objective level) := by
  apply SpaceDecider.of_computable (ImplicitGraph.connected_computable (edge_computable hP hd ho hl hA)
    (valid_computable hP hd ho hl hA) (width_unary hP hd ho hl hA))
  intro q
  simp only [connectedLanguage, Set.mem_ofPred_eq, decide_eq_true_eq]

end LeanCanny.Encoding.CoordinateAffineTerminalGraph
