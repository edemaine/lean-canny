/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralPrefixSquareSample

/-! # Literal scalar-only framed runs feed the complete square factory

Each root keeps its actual script, initial state and source changes. The
fixed schedule is proved by interpretation. Only the frontend's original
row mass bound and charged coefficient reader remain for native access.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedSquareSample
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralHistorySampler
open IntegralMixedFramedHistoryScript
open scoped Classical

variable {ambient horizon width : List Bool→ℕ}
variable {P : (u : List Bool)→SpatialSource (ambient u)}

noncomputable def family (initial : (u : List Bool)→State (P u) (horizon u) (width u) 0 (Fin 0))
    (cs : (u : List Bool)→List (Instruction (ambient u) (width u)))
    (hcs : ∀ u,(cs u).length≤horizon u+1)
    (h0 : ∀ u,Scheduled (initial u).sampler)
    (hc : ∀ u, ∀ c∈cs u,c.command.isCritical=false)
    (hpos : ∀ u,0<(cs u).length) (mass : List Bool→ℕ)
    (hmass : ∀ u i,MvMass.mass ((run (initial u) (cs u) (hcs u)).sampler.scalarPrefix.rows i)≤2^mass u) :
    IntegralPrefixSquareSample.Family where
  horizon := horizon
  width := width
  count u := (cs u).length
  mass := mass
  prefixAt u := (run (initial u) (cs u) (hcs u)).sampler.scalarPrefix
  count_pos := hpos
  scheduled u := scheduled_run (initial u) (h0 u) (cs u) (hcs u) (hc u)
  row_mass := hmass

theorem input_rows (initial : (u : List Bool)→State (P u) (horizon u) (width u) 0 (Fin 0))
    (cs : (u : List Bool)→List (Instruction (ambient u) (width u)))
    (hcs : ∀ u,(cs u).length≤horizon u+1) (h0 : ∀ u,Scheduled (initial u).sampler)
    (hc : ∀ u, ∀ c∈cs u,c.command.isCritical=false) (hpos : ∀ u,0<(cs u).length)
    (mass : List Bool→ℕ)
    (hmass : ∀ u i,MvMass.mass ((run (initial u) (cs u) (hcs u)).sampler.scalarPrefix.rows i)≤2^mass u)
    (u : List Bool) (i : Fin (cs u).length) :
    (IntegralPrefixSquareSample.input (family initial cs hcs h0 hc hpos mass hmass)).system u i=
      (run (initial u) (cs u) (hcs u)).sampler.scalarPrefix.rows i := rfl

theorem complete (initial : (u : List Bool)→State (P u) (horizon u) (width u) 0 (Fin 0))
    (cs : (u : List Bool)→List (Instruction (ambient u) (width u)))
    (hcs : ∀ u,(cs u).length≤horizon u+1) (h0 : ∀ u,Scheduled (initial u).sampler)
    (hc : ∀ u, ∀ c∈cs u,c.command.isCritical=false) (hpos : ∀ u,0<(cs u).length)
    (mass : List Bool→ℕ)
    (hmass : ∀ u i,MvMass.mass ((run (initial u) (cs u) (hcs u)).sampler.scalarPrefix.rows i)≤2^mass u) :
    SquareSampleComplete.Complete
      (IntegralPrefixSquareSample.input (family initial cs hcs h0 hc hpos mass hmass)) :=
  IntegralPrefixSquareSample.complete _

end LeanCanny.Encoding.IntegralFramedSquareSample
