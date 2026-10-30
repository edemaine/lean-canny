/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphContextInterval
public import LeanCanny.Encoding.FlatAffineEndpointMarkerComplete

/-! # Every bounded original gap has an accepted native slab context -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphContext
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord endpointWord sampleWord)
open OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def record (s g a t b u : List Bool) : List Bool := pair (pair s g) (pair (pair a t) (pair b u))
theorem record_source (s g a t b u : List Bool) : source (record s g a t b u) = s := by
  simp only [record, source, pairFst_pair]
theorem record_gap (s g a t b u : List Bool) : gapWord (record s g a t b u) = g := by
  simp only [record, gapWord, pairFst_pair, pairSnd_pair]
theorem record_endpoint (side : Bool) (s g a t b u : List Bool) :
    endpointWord side (record s g a t b u) = if side then b else a := by
  cases side <;> simp only [record, endpointWord, FlatAffineSlabGraphCodes.side, pairFst_pair, pairSnd_pair,
    Bool.false_eq_true, ite_false, ite_true]
theorem record_sample (side : Bool) (s g a t b u : List Bool) :
    sampleWord side (record s g a t b u) = if side then u else t := by
  cases side <;> simp only [record, sampleWord, FlatAffineSlabGraphCodes.side, pairFst_pair, pairSnd_pair,
    Bool.false_eq_true, ite_false, ite_true]

theorem side_labels (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (right : Bool) (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (i : Fin (FlatAffineEndpointSampleSlab.roots F cone height s).card)
    (j : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card)
    (he : root (FlatAffineEndpointSampleSlab.roots F cone height s) i = root (FlatAffineEndpointCells.roots F cone height (pairFst s)) j)
    (hg : (if right then rightGap _ i else leftGap _ i) = k)
    (h0 : 0 < (if right then rightGap _ j else leftGap _ j).val)
    (hk : (if right then rightGap _ j else leftGap _ j).val < (FlatAffineEndpointCells.roots F cone height (pairFst s)).card) :
    ∃ a t, pair (pair (pairFst s) a) t ∈ FlatAffineEndpointAdjacentSamples.language F cone height right ∧
      FlatAffineEndpointSampleSlab.numeric F cone height (pair (pair s []) (pair t (BinaryNatCode.encode k.val))) := by
  let a := root (FlatAffineEndpointSampleSlab.roots F cone height s) i
  have HA : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0 :=
    (FlatAffineHeightCells.mem_roots_iff F cone height (pairFst (pairFst s)) a).mp (root_mem _ i)
  obtain ⟨aw, haw, hea⟩ := IntegerPolynomialSampleInput.root_complete (FlatAffineEndpointAdjacentSamples.heightSource F cone height)
    (pairFst s) (FlatAffineHeightSlabExceptional.ne_zero F cone height (pairFst (pairFst s))) a HA
  obtain ⟨t, ht, htg⟩ := FlatAffineEndpointSamples.exists_in_gap F cone height (pairFst s) hs.1 a HA _ h0 hk
  have HN := FlatAffineEndpointSamples.source_ne_zero F cone height (pairFst s) hs.1 a HA
  obtain ⟨tw, htw, het, hadj⟩ := IntegerPolynomialAdjacentSamples.sample_label_complete_point
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (FlatAffineEndpointSamples.source F cone height)
    (FlatAffineEndpointCells.source F cone height) right (pairFst s) aw haw j (he.symm.trans hea.symm) t HN
    ((FlatAffineEndpointSamples.mem_roots_iff F cone height (pairFst s) hs.1 a HA t).mp ht) htg
  have HSUB : t ∈ gap (FlatAffineEndpointSampleSlab.roots F cone height s) k := by
    have HS : FlatAffineEndpointSampleSlab.roots F cone height s ⊆ FlatAffineEndpointCells.roots F cone height (pairFst s) := by
      intro x hx
      exact FlatAffineEndpointCells.endpoint_mem F cone height (pairFst s) hs.1 x
        ((FlatAffineHeightCells.mem_roots_iff F cone height (pairFst (pairFst s)) x).mp hx)
    rw [← hg]
    cases right
    · exact leftGap_refines _ _ HS i j he htg
    · exact rightGap_refines _ _ HS i j he htg
  refine ⟨aw, tw, ?_, ?_⟩
  · exact ⟨by simpa only [pairFst_pair] using hs.1, hadj⟩
  · apply (FlatAffineEndpointSampleSlab.numeric_packet F cone height s [] tw htw k).mpr
    have HET : (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) tw htw).val (0 : Fin 1) = t := het
    rw [HET]
    exact (mem_gap_iff_rank _ _ _).mp HSUB

theorem complete_record (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointSampleSlab.roots F cone height s).card) :
    ∃ a t b u, record s (BinaryNatCode.encode k.val) a t b u ∈ language F cone height := by
  let S := FlatAffineEndpointSampleSlab.roots F cone height s
  let T := FlatAffineEndpointCells.roots F cone height (pairFst s)
  let l : Fin S.card := ⟨k.val - 1, by dsimp only [S]; omega⟩
  let r : Fin S.card := ⟨k.val, hk⟩
  have HS : S ⊆ T := by
    intro x hx
    exact FlatAffineEndpointCells.endpoint_mem F cone height (pairFst s) hs.1 x
      ((FlatAffineHeightCells.mem_roots_iff F cone height (pairFst (pairFst s)) x).mp hx)
  obtain ⟨i, hi⟩ := exists_root T (root S l) (HS (root_mem S l))
  obtain ⟨j, hj⟩ := exists_root T (root S r) (HS (root_mem S r))
  have HIJ : i < j := (root_strictMono T).lt_iff_lt.mp (by
    rw [hi, hj]
    apply root_strictMono S
    change k.val - 1 < k.val
    omega)
  obtain ⟨a, t, hL, nL⟩ := side_labels F cone height s hs true k l i hi.symm
    (by apply Fin.ext; change k.val - 1 + 1 = k.val; omega)
    (by change 0 < i.val + 1; omega)
    (by change i.val + 1 < T.card; have := j.isLt; change i.val < j.val at HIJ; omega)
  obtain ⟨b, u, hR, nR⟩ := side_labels F cone height s hs false k r j hj.symm
    (Fin.ext rfl) (by change 0 < j.val; change i.val < j.val at HIJ; omega) j.isLt
  refine ⟨a, t, b, u, ?_⟩
  simp only [language, Set.mem_ofPred_eq, adjacentQuery, numericQuery, record_source,
    record_gap, record_endpoint, record_sample, Bool.false_eq_true, ite_false, ite_true]
  exact ⟨hs, hL, hR, nL, nR⟩

theorem complete (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (k : Fin ((FlatAffineEndpointSampleSlab.roots F cone height s).card + 1))
    (h0 : 0 < k.val) (hk : k.val < (FlatAffineEndpointSampleSlab.roots F cone height s).card) :
    ∃ c, c ∈ language F cone height ∧ source c = s ∧ gapWord c = BinaryNatCode.encode k.val := by
  obtain ⟨a, t, b, u, hc⟩ := complete_record F cone height s hs k h0 hk
  exact ⟨_, hc, record_source _ _ _ _ _ _, record_gap _ _ _ _ _ _⟩

end LeanCanny.Encoding.FlatAffineSlabGraphContext
