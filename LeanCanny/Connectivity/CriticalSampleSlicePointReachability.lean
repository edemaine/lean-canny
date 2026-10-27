/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Connectivity.CriticalSampleSlicePointLocation
public import LeanCanny.Connectivity.CriticalSampleSliceBooleanReachability

/-! # Native point paths with internally constructed endpoint labels

Two native comparison polynomials locate the endpoints in the existing
cell cover. Graph reachability then tests their path connection in the
actual Boolean solution set. Endpoints outside that set are rejected,
including an excluded root queried against itself.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CriticalSampleSlicePointReachability
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation
open BoundedFullWriter BoundedCriticalSampleSlice CriticalSampleSliceCellCover CriticalSampleSliceBooleanAtoms
open BoundedAlgebraicSlice (Family)
open scoped Classical

theorem vertex_at_point (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool)
    (hu : u ∈ valid P) (i : Index P Q u) (a : ℝ) (hi : a ∈ piece P Q u i) :
    CriticalSampleSliceBooleanPSPACE.vertex P Q S u (CriticalSampleSliceCellLabels.label P Q u i) = true ↔
      a ∈ solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u)) := by
  rw [CriticalSampleSliceBooleanPSPACE.vertex, decide_eq_true_eq]
  change (_ ∧ _) ↔ _
  rw [and_iff_right (CriticalSampleSliceCellLabels.label_valid P Q u hu i),
    CriticalSampleSliceBooleanCells.value_packet P Q S u hu i a hi]
  rfl

theorem label_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (S : Source) (u : List Bool)
    (hu : u ∈ valid P) (i j : Index P Q u) (a b : ℝ)
    (hi : a ∈ piece P Q u i) (hj : b ∈ piece P Q u j) :
    pair u (pair (CriticalSampleSliceCellLabels.label P Q u i) (CriticalSampleSliceCellLabels.label P Q u j)) ∈
      CriticalSampleSliceBooleanReachability.language P Q S ↔
        JoinedIn (solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u))) a b := by
  have H (ha : a ∈ solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u)))
      (hb : b ∈ solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u))) :
      pair u (pair (CriticalSampleSliceCellLabels.label P Q u i) (CriticalSampleSliceCellLabels.label P Q u j)) ∈
        CriticalSampleSliceBooleanReachability.language P Q S ↔
          JoinedIn (solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u))) a b := by
    let a' : solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u)) := ⟨a, ha⟩
    let b' : solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u)) := ⟨b, hb⟩
    have h := CriticalSampleSliceBooleanReachability.packet P Q S u hu i j (x := a') (y := b') hi hj
    rw [joinedIn_univ] at h
    exact h.trans (joinedIn_iff_joined ha hb).symm
  constructor
  · intro h
    have hv := h.2.2.2
    simp only [CriticalSampleSliceBooleanReachability.leftWord, CriticalSampleSliceBooleanReachability.rightWord,
      pairFst_pair, pairSnd_pair] at hv
    have ha := (vertex_at_point P Q S u hu i a hi).mp hv.1
    have hb := (vertex_at_point P Q S u hu j b hj).mp hv.2.1
    exact (H ha hb).mp h
  · intro h
    exact (H h.source_mem h.target_mem).mpr h

noncomputable def query (P : Readers) (Q : BivariateQueryProductBits.Family) (F G : Family) (u : List Bool) : List Bool :=
  pair u (pair (CriticalSampleSlicePointLocation.locate P Q F u) (CriticalSampleSlicePointLocation.locate P Q G u))

theorem query_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) {F G : Family} (B : F.Access) (C : G.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (query P Q F G) :=
  ((CriticalSampleSlicePointLocation.evaluator h A B ha).pairOutputs
    (CriticalSampleSlicePointLocation.evaluator h A C ha)).withInput

noncomputable def language (P : Readers) (Q : BivariateQueryProductBits.Family) (F G : Family) (S : Source) : Language :=
  query P Q F G ⁻¹' CriticalSampleSliceBooleanReachability.language P Q S

theorem decider {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) {F G : Family} (B : F.Access) (C : G.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (D : Access S) :
    SpaceDecider (language P Q F G S) := by
  apply SpaceDecider.of_computable ((CriticalSampleSliceBooleanReachability.decider h A ha S D).computable.comp
    (query_evaluator h A B C ha).computable)
  intro u
  simp only [language, Set.mem_preimage, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) {F G : Family} (B : F.Access) (C : G.Access)
    (ha : ∀ c, (ETR.TermView.term (P.source c)).arity ≤ P.dim c) (S : Source) (D : Access S) :
    language P Q F G S ∈ PSPACE := (decider h A B C ha S D).mem_PSPACE

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (F G : Family) (S : Source)
    (u : List Bool) (hu : u ∈ valid P) (a b : ℝ)
    (hF : ∀ t : ℝ, SignType.sign ((specialized P F u).eval t) = SignType.sign (t - a))
    (hG : ∀ t : ℝ, SignType.sign ((specialized P G u).eval t) = SignType.sign (t - b)) :
    u ∈ language P Q F G S ↔ JoinedIn (solutionSet P Q u (CriticalSampleSliceBooleanCells.truth S (context u))) a b := by
  obtain ⟨i, hi⟩ := Geometry.OrderedRealCells.cover (roots P Q u) a
  obtain ⟨j, hj⟩ := Geometry.OrderedRealCells.cover (roots P Q u) b
  change query P Q F G u ∈ CriticalSampleSliceBooleanReachability.language P Q S ↔ _
  rw [query, CriticalSampleSlicePointLocation.packet P Q F u a hF i hi,
    CriticalSampleSlicePointLocation.packet P Q G u b hG j hj]
  exact label_packet P Q S u hu i j a b hi hj

theorem invalid_base (P : Readers) (Q : BivariateQueryProductBits.Family) (F G : Family) (S : Source)
    (u : List Bool) (hu : u ∉ valid P) : u ∉ language P Q F G S :=
  CriticalSampleSliceBooleanReachability.invalid_base P Q S u _ _ hu

end LeanCanny.Connectivity.CriticalSampleSlicePointReachability
