/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.ClosedFormulaGateMetadata
public import LeanCanny.Connectivity.MonotoneGateDescription
/-! # Literal canonical inputs generate native bounded-source reader records -/
@[expose] public section
namespace LeanCanny.Encoding.ClosedFormulaGateMetadata
open LeanCanny.Computation LeanCanny.Connectivity ETR

noncomputable def readers (radius : List Bool → ℕ) : BoundedFullWriter.Readers := MonotoneGateGraph.readers family radius

theorem readers_polyTime (radius : List Bool → ℕ) (hR : BinaryFn radius) : (readers radius).PolyTime :=
  MonotoneGateGraph.readers_polyTime family access radius hR

theorem readers_scope (radius : List Bool → ℕ) :
    ∀ c, (TermView.term ((readers radius).source c)).arity≤(readers radius).dim c := by
  apply MonotoneGateGraph.readers_scope
  intro c i _
  simpa only [family,pairFst_pair] using atom_scope (pair c (List.replicate i true))

noncomputable def description (c : List Bool) : Description := MonotoneGateGraph.description family c

theorem description_wellFormed (c : List Bool) : (description c).WellFormed := by
  apply MonotoneGateGraph.description_wellFormed
  intro i _
  simpa only [family,pairFst_pair] using atom_scope (pair c (List.replicate i true))

theorem whole_record_FP : (fun c => (Input.whole (description c)).encode) ∈ FP :=
  MonotoneGateGraph.whole_record_FP family access

end LeanCanny.Encoding.ClosedFormulaGateMetadata
