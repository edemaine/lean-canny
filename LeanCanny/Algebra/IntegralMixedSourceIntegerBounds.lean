/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerLookup
public import LeanCanny.Algebra.IntegerPolynomialFiniteMassEnvelope
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # Source mass bounds imply actual integer-prelude family bounds -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem uniform_script {n S B W D L f C : ℕ} (cs : List (Instruction n B))
    (hc : ∀c∈cs,InstructionBounds (C+1) f W D L c) : ScriptBounds S W D L f C cs := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    refine ⟨ih (fun d hd=>hc d (List.mem_cons_of_mem c hd)),?_⟩
    exact instruction_bounds_mono (source_le_height n S B W D L f C _) (hc c List.mem_cons_self)

theorem instruction_bounds (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (Q root).degree≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (root : List Bool) (i : Fin (count root)) (G f L : ℕ)
    (hb : InstructionBounds G f (P.sourceWidth root) (P.degree root) L
      (⟨Q root,hq root,IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction (P.ambient root) (P.width root)))
    (hm : ∀j<count root,S.mass (pair root (BinaryNatCode.encode j))≤f*G+1) :
    InstructionBounds G f (P.sourceWidth root) (P.degree root) L (instruction P Q hq S count hz hd root i) where
  low := hb.low
  leading := hb.leading
  width := hb.width
  degree := hb.degree
  auxiliary := hb.auxiliary
  command k := ((coeff_natAbs_le_coefficientMass _ k).trans (S.mass_bound _)).trans
    (Nat.pow_le_pow_right (by decide) (hm _ (by have H:=i.isLt; omega)))

theorem family_inputs (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
    (hdegree : ∀root,(Q root).degree=P.degree root)
    (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
    (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
    (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
    (hroom : ∀root,count root+2≤P.cap root+1) (nodes factor seed : List Bool → ℕ)
    (hb : ∀root,InstructionBounds (seed root+1) (factor root) (P.sourceWidth root) (P.degree root) (nodes root)
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (plan P Q hdegree hcap S count hz hd hroom) root))
    (hm : ∀root j,j<count root→S.mass (pair root (BinaryNatCode.encode j))≤factor root*(seed root+1)+1) :
    FamilyInputs P (plan P Q hdegree hcap S count hz hd hroom) nodes factor seed where
  default := hb
  script root := by
    apply uniform_script
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact instruction_bounds P Q _ S count hz hd root i _ _ _ (hb root) (hm root)

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
