/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointSample
public import LeanCanny.Encoding.IntegralMixedRoadmapFirstSeedReplay
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSize
/-! # Actual bounded joint words exist for genuine joint-source candidates

This samples the literal core source. It makes no claim that grid membership
or a cut-free interval persists under moving to a component sample.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSample
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "HN" => FormulaSignSlotRadialJointLayout.dimension_unary
local notation "HT" => FormulaSignSlotRadialJointCore.equation_FP
local notation "HA" => FormulaSignSlotRadialJointCore.scope
attribute [local irreducible] radius FormulaSignSlotRadialJointCore.equation
  FormulaSignSlotRadialJointLayout.dimension IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.Valid IntegralMixedRoadmapMarkedPrelude.Replay

theorem exists_replay_sample (u label : List Bool)
    (hg : AuxiliaryCandidateComponentCover.Good HN HT HA u label) :
    ∃ p : List Bool, ∃ _hv : Valid p, Replay p ∧ header p = u ∧
      IntegralMixedRoadmapAtomic.candidate (node p) = pair u label ∧ metadata p = [] := by
  have HRadius : IntegralMixedAuxiliaryCandidateRadius.radius HN HT HA u ≤ radius u := by
    unfold radius
    exact le_refl _
  obtain ⟨x, HX, HG⟩ := IntegralMixedRoadmapGraph.exists_first_critical HN HT HA radius_binary
    u label hg HRadius
  obtain ⟨w, _, HV, _, HR⟩ := IntegralMixedRoadmapFirstSeed.exists_at_replay HN HT HA radius_binary
    u label hg HRadius x HX HG
  let q := IntegralMixedRoadmapAtomic.packet (pair u label)
    (IntegralMixedRoadmapSeedResampling.payload (FormulaSignSlotRadialJointLayout.dimension u+3)) w
  refine ⟨pair q [], ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Valid, node, pairFst_pair, q] using HV
  · simpa only [Replay, node, pairFst_pair, q] using HR
  · simp only [header, headerContext, node, pairFst_pair, IntegralMixedAuxiliaryMarkedIntegerSource.original,
      IntegralMixedAuxiliaryMarkedIntegerSource.candidate, q, IntegralMixedRoadmapAtomic.root,
      IntegralMixedRoadmapAtomic.candidate, IntegralMixedRoadmapAtomic.packet]
  · simp only [node, pairFst_pair, q, IntegralMixedRoadmapAtomic.packet,
      IntegralMixedRoadmapAtomic.candidate]
  · exact pairSnd_pair _ _

noncomputable def sourcePoint (u : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation u).eval env = 0) :
    AuxiliaryCandidateComponentCover.Space FormulaSignSlotRadialJointLayout.dimension
      FormulaSignSlotRadialJointCore.equation u := by
  refine ⟨fun i => env i.val, ?_⟩
  change (AuxiliaryTiltedTerm.polynomial (FormulaSignSlotRadialJointLayout.dimension u)
    (FormulaSignSlotRadialJointCore.equation u)).eval (fun i => env i.val) = 0
  rw [AuxiliaryCandidateComponentCover.evaluation]
  have HE := (FormulaSignSlotRadialJointCore.equation u).eval_congr
    (Formula.extend (fun i : Fin (FormulaSignSlotRadialJointLayout.dimension u) => env i.val)) env (by
      intro i hi
      simp only [Formula.extend, dite_eq_left (hi.trans_le (FormulaSignSlotRadialJointCore.scope u))])
  exact HE.trans h

/-- Actual component sampling supplies a genuine original candidate, not a
caller-selected evaluator or an arbitrary algebraic point code. -/
theorem exists_good_joined (u : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation u).eval env = 0) :
    ∃ i : Vertex (IntegralMixedAuxiliaryCandidate.labelWidth HN HT HA u),
      ∃ hg : AuxiliaryCandidateComponentCover.Good HN HT HA u i.val,
        JoinedIn Set.univ (sourcePoint u env h)
          (AuxiliaryCandidateComponentCover.sample HN HT HA u ⟨i,hg⟩) := by
  let C := AuxiliaryCandidateComponentCover.cover HN HT HA u
  obtain ⟨i, HI⟩ := C.cover (sourcePoint u env h)
  have HG := (AuxiliaryCandidateComponentCover.nonempty_iff_good HN HT HA u i).mp
    ⟨sourcePoint u env h, HI⟩
  have HS : AuxiliaryCandidateComponentCover.sample HN HT HA u ⟨i,HG⟩ ∈ C.piece i := by
    change AuxiliaryCandidateComponentCover.sample HN HT HA u ⟨i,HG⟩ ∈
      SampledBitComponentCover.piece (AuxiliaryCandidateComponentCover.samples HN HT HA u) i
    rw [SampledBitComponentCover.piece_of_good _ _ HG]
    exact mem_connectedComponent
  exact ⟨i, HG, (C.paths i _ HI _ HS).mono (Set.subset_univ _)⟩

theorem exists_replay_of_root (u : List Bool) (env : ℕ → ℝ)
    (h : (FormulaSignSlotRadialJointCore.equation u).eval env = 0) :
    ∃ p : List Bool, ∃ _hv : Valid p, Replay p ∧ header p = u := by
  obtain ⟨i, HG, _⟩ := exists_good_joined u env h
  obtain ⟨p, HV, HR, HH, _⟩ := exists_replay_sample u i.val HG
  exact ⟨p, HV, HR, HH⟩

theorem original_word_budget : ∃ P : Polynomial ℕ, ∀ p : List Bool, Valid p →
    (word p).length ≤ P.eval (header p).length := by
  obtain ⟨P, HP⟩ := IntegralMixedRoadmapAtomic.wordBudget_polynomial HN HT HA radius_binary
  refine ⟨P, fun p hv => ?_⟩
  have HW := (IntegralMixedRoadmapAtomic.word_bound HN HT HA radius_binary (node p) hv).trans (HP (node p))
  have HH : header p = IntegralMixedRoadmapAtomic.original (node p) := by
    simp only [header, headerContext, pairFst_pair, IntegralMixedRoadmapMarkedPrelude.original_root]
  rw [HH]
  exact HW

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
