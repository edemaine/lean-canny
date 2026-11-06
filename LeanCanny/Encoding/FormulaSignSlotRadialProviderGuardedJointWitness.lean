/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderJointWitnessNative
/-! # A native guard is checked on the two-label witness's same complete word

This assembly reuses the original header budget. Its lower-level guard
language receives exactly the existing sampler query, with no resampling.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderGuardedJointWitness
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def rawLanguage (G : Language) : Language :=
  {q | q ∈ FormulaSignSlotRadialProviderJointWitness.rawLanguage ∧ FormulaSignSlotRadialProviderJointWitness.sampleQuery q ∈ G}
theorem raw_decider (G : Language) (D : SpaceDecider G) : SpaceDecider (rawLanguage G) := by
  have EG := (D.precompose FormulaSignSlotRadialProviderJointWitness.sampleQuery FormulaSignSlotRadialProviderJointWitness.sampleQuery_FP).flagEvaluator
  apply (FormulaSignSlotRadialProviderJointWitness.raw_decider.flagEvaluator.andFlags EG).decider (fun v => decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [rawLanguage,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def Bounded (G : Language) (H : List Bool) : Prop :=
  ∃ bits : List Bool,bits.length=FormulaSignSlotRadialProviderJointWitness.width H ∧ FormulaSignSlotRadialProviderJointWitness.probe (pair H bits) ∈ rawLanguage G
noncomputable def language (G : Language) : Language := {H | Bounded G H}
theorem evaluator (G : Language) (D : SpaceDecider G) : SpaceFunction (fun H => [decide (Bounded G H)]) := by
  have E := ((raw_decider G D).precompose FormulaSignSlotRadialProviderJointWitness.probe FormulaSignSlotRadialProviderJointWitness.probe_FP).flagEvaluator.exists_words FormulaSignSlotRadialProviderJointWitness.width_unary
  exact E.congr (funext fun H => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Bounded,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq])
theorem decider (G : Language) (D : SpaceDecider G) : SpaceDecider (language G) := by
  apply (evaluator G D).decider (fun v => decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro H
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE (G : Language) (D : SpaceDecider G) : language G ∈ PSPACE := (decider G D).mem_PSPACE

private theorem sample_packet (H : List Bool) (k : ℕ) (Gamma w aL eL aR eR : List Bool) :
    FormulaSignSlotRadialProviderJointWitness.sampleQuery (FormulaSignSlotRadialProviderJointWitness.packet H k Gamma w aL eL aR eR) =
      pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w := by
  obtain ⟨HH,HK,HG,HW,_HL,_HR⟩ := FormulaSignSlotRadialProviderJointWitness.packet_readers H k Gamma w aL eL aR eR
  simp only [FormulaSignSlotRadialProviderJointWitness.sampleQuery,FormulaSignSlotRadialProviderJointWitness.stratum,HH,HK,HG,HW]

attribute [local irreducible] FormulaSignSlotRadialProviderJointWitness.header
  FormulaSignSlotRadialProviderJointWitness.kind FormulaSignSlotRadialProviderJointWitness.gamma
  FormulaSignSlotRadialProviderJointWitness.ownWord FormulaSignSlotRadialProviderJointWitness.oldSeed
  FormulaSignSlotRadialProviderJointWitness.externalSeed FormulaSignSlotRadialProviderJointWitness.probe
  FormulaSignSlotRadialProviderJointWitness.stratum FormulaSignSlotRadialProviderJointWitness.sampleQuery
  FormulaSignSlotRadialProviderJointWitness.packet FormulaSignSlotRadialProviderJointWitness.data

/-- The guard and both seed pairs concern the exact same k, Gamma and OWN word. -/
theorem language_iff (G : Language) (H : List Bool) : H ∈ language G ↔
    ∃ k : ℕ,∃ Gamma w aL eL aR eR : List Bool,
      FormulaSignSlotRadialProviderJointWitness.Witness H k Gamma w aL eL aR eR ∧
      pair (pair (FormulaSignSlotRadialJointStratum.packet H k) Gamma) w ∈ G := by
  change (∃ bits : List Bool,bits.length=FormulaSignSlotRadialProviderJointWitness.width H ∧ FormulaSignSlotRadialProviderJointWitness.probe (pair H bits) ∈ rawLanguage G) ↔ _
  constructor
  · rintro ⟨bits,_HB,HQ,HG⟩
    let z := FormulaSignSlotRadialProviderJointWitness.probe (pair H bits)
    have HH : FormulaSignSlotRadialProviderJointWitness.header z = H := by simp only [z,FormulaSignSlotRadialProviderJointWitness.header,FormulaSignSlotRadialProviderJointWitness.probe,pairFst_pair]
    have HW : FormulaSignSlotRadialProviderJointWitness.Witness (FormulaSignSlotRadialProviderJointWitness.header z) (FormulaSignSlotRadialProviderJointWitness.kind z) (FormulaSignSlotRadialProviderJointWitness.gamma z) (FormulaSignSlotRadialProviderJointWitness.ownWord z)
      (FormulaSignSlotRadialProviderJointWitness.oldSeed false z) (FormulaSignSlotRadialProviderJointWitness.externalSeed false z) (FormulaSignSlotRadialProviderJointWitness.oldSeed true z) (FormulaSignSlotRadialProviderJointWitness.externalSeed true z) := HQ
    refine ⟨FormulaSignSlotRadialProviderJointWitness.kind z,FormulaSignSlotRadialProviderJointWitness.gamma z,FormulaSignSlotRadialProviderJointWitness.ownWord z,FormulaSignSlotRadialProviderJointWitness.oldSeed false z,FormulaSignSlotRadialProviderJointWitness.externalSeed false z,
      FormulaSignSlotRadialProviderJointWitness.oldSeed true z,FormulaSignSlotRadialProviderJointWitness.externalSeed true z,HH ▸ HW,?_⟩
    change FormulaSignSlotRadialProviderJointWitness.sampleQuery z ∈ G at HG
    simpa only [FormulaSignSlotRadialProviderJointWitness.sampleQuery,FormulaSignSlotRadialProviderJointWitness.stratum,HH] using HG
  · rintro ⟨k,Gamma,w,aL,eL,aR,eR,HW,HG⟩
    have HB : (FormulaSignSlotRadialProviderJointWitness.data (FormulaSignSlotRadialProviderJointWitness.packet H k Gamma w aL eL aR eR)).length ≤ FormulaSignSlotRadialProviderJointWitness.rawBudget H := by
      obtain ⟨HK,HT,HWd,HA,HE,HA',HE'⟩ := HW.1
      exact FormulaSignSlotRadialProviderJointWitness.packet_length H k Gamma w aL eL aR eR HK HT HWd HA HE HA' HE'
    let bits := IntegralMixedRoadmapWordLabel.encode (FormulaSignSlotRadialProviderJointWitness.rawBudget H) (FormulaSignSlotRadialProviderJointWitness.data (FormulaSignSlotRadialProviderJointWitness.packet H k Gamma w aL eL aR eR))
    refine ⟨bits,IntegralMixedRoadmapWordLabel.encode_length _ _ HB,?_⟩
    have HE : FormulaSignSlotRadialProviderJointWitness.probe (pair H bits) = FormulaSignSlotRadialProviderJointWitness.packet H k Gamma w aL eL aR eR := by
      simp only [FormulaSignSlotRadialProviderJointWitness.probe,pairFst_pair,pairSnd_pair,bits,IntegralMixedRoadmapWordLabel.decode_encode,FormulaSignSlotRadialProviderJointWitness.data,FormulaSignSlotRadialProviderJointWitness.packet]
    rw [HE]
    exact ⟨(FormulaSignSlotRadialProviderJointWitness.raw_packet_iff H k Gamma w aL eL aR eR).mpr HW,(sample_packet H k Gamma w aL eL aR eR).symm ▸ HG⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderGuardedJointWitness
