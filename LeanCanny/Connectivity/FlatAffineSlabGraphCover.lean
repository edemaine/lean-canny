/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.FlatAffineSlabGraphGeometryEdges
public import LeanCanny.Connectivity.BitFrontierCover
public import LeanCanny.Encoding.FlatAffineSlabGraphAlgorithms

/-! # The native graph is an accessible cover of the actual closed slab

Invalid words denote empty pieces. Every valid word denotes its unique actual
curve or endpoint point; arbitrary padding and duplicate markers are harmless.
All relative frontier edges agree with the graph's native adjacency routine.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineSlabGraphBranches
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes
open FlatAffineSlabGraphArcs (equation)
open FlatAffineSlabGraphContext (endpointValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local irreducible] FlatAffineSlabGraph.validLanguage FlatAffineSlabGraph.edgeLanguage

abbrev Space (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (c : List Bool) :=
  SlabCover.Space (equation F height c) (endpointValue F cone height false c) (endpointValue F cone height true c)

variable {F : Inputs} {cone : FlatAffinePowerPositive.ConeCertificate F}
  {height : (u : List Bool) → Fin (count F u)} {c : List Bool}
  [Fintype (FlatAffineSlabGraphArcs.Index F cone height c)] [LinearOrder (FlatAffineSlabGraphArcs.Index F cone height c)]

noncomputable def Family.piece (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (w : Vertex (width F cone height c)) : Set (Space F cone height c) :=
  if hv : pair c w.val ∈ FlatAffineSlabGraph.validLanguage F cone height then
    FiniteFiberSlab.piece (equation F height c) B.curve (endpointValue F cone height false c) (endpointValue F cone height true c)
      (Classical.choose ((B.valid_iff_denotes hc w.val).mp hv))
  else ∅

theorem Family.piece_eq (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) (w : Vertex (width F cone height c))
    (i : PieceIndex F cone height c) (hi : B.Denotes w.val i) :
    B.piece hc w = FiniteFiberSlab.piece (equation F height c) B.curve
      (endpointValue F cone height false c) (endpointValue F cone height true c) i := by
  have HV := (B.valid_iff_denotes hc w.val).mpr ⟨i, hi⟩
  rw [Family.piece, dite_eq_left HV]
  rw [B.denotes_unique hc w.val (Classical.choose_spec ((B.valid_iff_denotes hc w.val).mp HV)) hi]

noncomputable def Family.cover (B : Family F cone height c)
    (hc : c ∈ FlatAffineSlabGraphContext.language F cone height) :
    BitFrontierCover (Space F cone height c) (width F cone height c)
      (FlatAffineSlabGraph.edge F cone height c) (FlatAffineSlabGraph.valid F cone height c) where
  piece := B.piece hc
  cover z := by
    obtain ⟨i, hi⟩ := FiniteFiberSlab.cover (equation F height c) B.curve
      (fun t ht x hx => by obtain ⟨j, hj, _⟩ := (B.complete ⟨t, ht⟩ x).mp hx; exact ⟨j, hj⟩) z
    obtain ⟨w, hw, hd⟩ := B.denotes_surjective hc i
    exact ⟨⟨w, hw⟩, (B.piece_eq hc ⟨w, hw⟩ i hd).symm ▸ hi⟩
  accessible w := by
    by_cases HV : pair c w.val ∈ FlatAffineSlabGraph.validLanguage F cone height
    · obtain ⟨i, hi⟩ := (B.valid_iff_denotes hc w.val).mp HV
      rw [B.piece_eq hc w i hi]
      exact FiniteFiberSlab.accessible (equation F height c) (FlatAffineSlabGraphContext.endpoints_lt F cone height c hc)
        B.curve B.continuous B.roots i
    · simp only [Family.piece, dite_eq_right HV]
      intro x hx
      simp only [closure_empty, Set.mem_empty_iff_false] at hx
  valid_iff w := by
    simp only [FlatAffineSlabGraph.valid, decide_eq_true_eq]
    constructor
    · intro HV
      obtain ⟨i, hi⟩ := (B.valid_iff_denotes hc w.val).mp HV
      rw [B.piece_eq hc w i hi]
      exact FiniteFiberSlab.nonempty_piece (equation F height c) (FlatAffineSlabGraphContext.endpoints_lt F cone height c hc)
        B.curve B.roots i
    · intro HN
      by_contra HV
      simp only [Family.piece, dite_eq_right HV, Set.not_nonempty_empty] at HN
  edge_iff w v := by
    simp only [FlatAffineSlabGraph.edge, decide_eq_true_eq]
    by_cases HW : pair c w.val ∈ FlatAffineSlabGraph.validLanguage F cone height
    · by_cases HV : pair c v.val ∈ FlatAffineSlabGraph.validLanguage F cone height
      · obtain ⟨i, hi⟩ := (B.valid_iff_denotes hc w.val).mp HW
        obtain ⟨j, hj⟩ := (B.valid_iff_denotes hc v.val).mp HV
        have P := FiniteFiberSlab.incident_iff (equation F height c) (FlatAffineSlabGraphContext.endpoints_lt F cone height c hc)
          B.curve B.continuous B.roots
          (fun t ht => B.injective ⟨t, ht⟩) i j
        have Q : FrontierCover.Incident (B.piece hc) w v ↔
            FrontierCover.Incident (FiniteFiberSlab.piece (equation F height c) B.curve
              (endpointValue F cone height false c) (endpointValue F cone height true c)) i j := by
          simp only [FrontierCover.Incident, B.piece_eq hc w i hi, B.piece_eq hc v j hj]
        exact (B.edge_iff hc w.val v.val i j hi hj).trans (P.symm.trans Q.symm)
      · have HE : pair c (pair w.val v.val) ∉ FlatAffineSlabGraph.edgeLanguage F cone height := by
          intro H
          unfold FlatAffineSlabGraph.edgeLanguage at H
          apply HV
          simpa only [rightVertex, pairFst_pair, pairSnd_pair] using H.2.1
        simp only [HE, false_iff]
        intro H
        have HN := (H.nonempty (B.piece hc)).2
        simp only [Family.piece, dite_eq_right HV, Set.not_nonempty_empty] at HN
    · have HE : pair c (pair w.val v.val) ∉ FlatAffineSlabGraph.edgeLanguage F cone height := by
        intro H
        unfold FlatAffineSlabGraph.edgeLanguage at H
        apply HW
        simpa only [leftVertex, pairFst_pair, pairSnd_pair] using H.1
      simp only [HE, false_iff]
      intro H
      have HN := (H.nonempty (B.piece hc)).1
      simp only [Family.piece, dite_eq_right HW, Set.not_nonempty_empty] at HN

end LeanCanny.Connectivity.FlatAffineSlabGraphBranches
