/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotNontrivialRadialSamples
/-! # Every nonsingleton projected piece has descriptors at all closure points -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialDescriptorSingleton
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.ETR Set
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (c : List Bool) (i : Vertex (CanonicalAuxiliaryCandidateCover.width c))
  (a : Fin (FormulaSignSlotSource.dimension c) → ℝ)
local notation "P" => FormulaSignSlotRadialAccess.projectedPiece c
  (LeanCanny.Connectivity.ClopenPathCover.piece (CanonicalAuxiliaryCandidateLabelLock.positiveCover c) i)

theorem exists_of_nontrivial (ha : a ∈ P) (hn : ∃ z ∈ P, z ≠ a) :
    Nonempty (FormulaSignSlotCandidateRadialDescriptor.Descriptor c i a) := by
  obtain ⟨r0,_,_,HB0,z0,_,HG0⟩ :=
    FormulaSignSlotNontrivialRadialSamples.arbitrarily_small_samples c i a ha hn 1 zero_lt_one
  obtain ⟨b,hb,HB⟩ := FormulaSignSlotRadialBranchCuts.small_interval c a r0 HB0 z0.val.val HG0
  obtain ⟨r,hr,hl,_,z,HZ,HG⟩ :=
    FormulaSignSlotNontrivialRadialSamples.arbitrarily_small_samples c i a ha hn b hb
  obtain ⟨hi,lift,HL,HJ⟩ := (CanonicalAuxiliaryCandidateLabelLock.positive_mem_iff c i _).mp HZ
  exact ⟨{
    bound := b
    bound_pos := hb
    parameter := ⟨r,hr,hl⟩
    anchor := z
    grid := HG
    cut_free := HB
    good := hi
    closedAnchor := lift
    anchor_projection := HL
    anchor_component := HJ
  }⟩

theorem closure_iff : a ∈ closure P ↔ P = {a} ∨
    Nonempty (FormulaSignSlotCandidateRadialDescriptor.Descriptor c i a) := by
  constructor
  · intro H
    by_cases HA : a ∈ P
    · by_cases HN : ∃ z ∈ P, z ≠ a
      · exact Or.inr (exists_of_nontrivial c i a HA HN)
      · left
        ext z
        constructor
        · intro HZ
          have HE : z = a := by
            by_contra HZNE
            exact HN ⟨z,HZ,HZNE⟩
          exact HE
        · intro HZ
          have HE : z = a := HZ
          exact HE.symm ▸ HA
    · exact Or.inr (FormulaSignSlotCandidateRadialDescriptor.exists_of_projected_boundary c i a H HA)
  · intro H
    rcases H with HS | HD
    · rw [HS]
      exact subset_closure (mem_singleton a)
    · exact HD.elim (fun D => D.mem_projected_closure)

end LeanCanny.Connectivity.FormulaSignSlotRadialDescriptorSingleton
