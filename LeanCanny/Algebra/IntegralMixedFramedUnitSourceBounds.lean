/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitBody
public import LeanCanny.Algebra.IntegralMixedFramedUnitSnapshot
public import LeanCanny.Algebra.IntegralMixedFramedStepHeight
public import LeanCanny.Algebra.IntegralMixedFramedOriginalBounds
public import LeanCanny.Algebra.IntegralMixedCausalLevelLowHeight
/-! # Literal unit records and tilted sources satisfy instruction bounds

Every retained-reference or zero row has one node and no nonzero integer
coefficient. Scales and sweep slopes are literally one. The actual tilted
LOW coefficient bound follows from its original AST and implicit level
exponent; no interpreted polynomial or matrix reader is a premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitSourceBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open scoped Classical

theorem expression_nodes (writer : List Bool → List Bool) (physical : Bool) (key : List Bool) (i : ℕ) :
    (IntegralMixedFramedUnitBodyBits.expression writer physical key i).nodes=1 := by
  unfold IntegralMixedFramedUnitBodyBits.expression
  split <;> rfl

theorem expression_coefficients (writer : List Bool → List Bool) (physical : Bool) (key : List Bool) (i C : ℕ) :
    (IntegralMixedFramedUnitBodyBits.expression writer physical key i).CoefficientsBound C := by
  unfold IntegralMixedFramedUnitBodyBits.expression
  split
  · trivial
  · exact Nat.zero_le C

theorem critical_command_bounds (P : Parameters) (writer : List Bool → List Bool) (physical : Bool)
    (key : List Bool) (offset : Fin (P.ambient (pairFst key)+1)) (objective coordinate C L B : ℕ)
    (Q : SpatialSource (P.ambient (pairFst key))) (hC : 1≤C) (hL : 1≤L) :
    IntegralMixedFullScriptHeight.CommandBounds C L
      (.critical (IntegralMixedFramedUnitBodyBits.critical P writer physical key offset objective coordinate) :
        IntegralMixedFullHistoryScript.Command Q B) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (expression_nodes writer physical key i.val).trans_le hL
  · intro i
    exact expression_coefficients writer physical key i.val C
  · intro i
    simpa only [IntegralMixedFramedUnitBodyBits.critical,Int.natAbs_one,Nat.size_one] using hC

theorem cut_command_bounds (P : Parameters) (writer : List Bool → List Bool)
    (key : List Bool) (offset : Fin (P.ambient (pairFst key)+1)) (objective coordinate C L B : ℕ)
    (hf : IntegralMixedFramedUnitBodyBits.height P writer key<offset.val)
    (Q : SpatialSource (P.ambient (pairFst key)))
    (kind : IntegralMixedRelativeCuts.Kind Q (IntegralMixedFramedUnitBodyBits.sweep P writer key offset objective coordinate hf))
    (d : ℕ) (ha : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) Q.degree)
    (hd : d≤2^B) (hC : 1≤C) (hL : 1≤L) :
    IntegralMixedFullScriptHeight.CommandBounds C L
      (.cut (IntegralMixedFramedUnitBodyBits.sweep P writer key offset objective coordinate hf) kind d ha hd) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    exact (expression_nodes writer false key i.val).trans_le hL
  · intro i
    exact expression_coefficients writer false key i.val C
  · intro i
    simpa only [IntegralMixedFramedUnitBodyBits.sweep,IntegralMixedFramedUnitBodyBits.critical,
      Int.natAbs_one,Nat.size_one] using hC
  · simpa only [IntegralMixedFramedUnitBodyBits.sweep,Int.natAbs_one,Nat.size_one] using hC

theorem snapshot_rule_bounds (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (writer : List Bool → List Bool)
    (hs : IntegralMixedFramedUnitSnapshotBits.Snapshot P D H writer)
    (key : List Bool) (C L : ℕ) (hC : 1≤C) (hL : 1≤L) :
    IntegralMixedFullHeightBits.RuleBounds C L ((IntegralMixedFramedHistoryFamilyBits.family P D H).rule key) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    rw [hs.virtualHeights key i]
    exact (expression_nodes writer false key i.val).trans_le hL
  · intro i
    rw [hs.virtualHeights key i]
    exact expression_coefficients writer false key i.val C
  · intro i
    rw [hs.virtualScales key i]
    simpa only [Int.natAbs_one,Nat.size_one] using hC
  · rw [hs.slope key]
    simpa only [Int.natAbs_one,Nat.size_one] using hC

theorem fallback_bounds (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (writer : List Bool → List Bool)
    (hs : IntegralMixedFramedUnitSnapshotBits.Snapshot P D H writer)
    (L C : List Bool → ℕ) (hL : ∀ root, 1≤L root) (key : List Bool) :
    IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C key := by
  have HB := snapshot_rule_bounds P D H writer hs key (C (pairFst key)+1) (L (pairFst key))
    (Nat.le_add_left 1 _) (hL (pairFst key))
  cases hc : (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command with
  | integer p hp hd =>
    simpa only [IntegralMixedFramedOriginalBounds.FallbackBounds,
      IntegralMixedFramedHistoryFamilyBits.family,IntegralMixedFramedHistoryFamilyBits.selection,hc] using HB
  | critical r =>
    simpa only [IntegralMixedFramedOriginalBounds.FallbackBounds,
      IntegralMixedFramedHistoryFamilyBits.family,IntegralMixedFramedHistoryFamilyBits.selection,hc] using HB
  | cut => simp only [IntegralMixedFramedOriginalBounds.FallbackBounds,hc]

theorem tilted_instruction_bounds {n k D T E f G B W D' L : ℕ} (u : Fin n) (t : ETR.Term)
    (ht : t.degreeBound≤D)
    (hcap : PurePowerReductionBounds.dimension (n+2) (FixedLeadingTiltedSource.degree D)≤2^B)
    (hsize : (FixedLeadingTiltedSource.lowTerm k D u.val t).toData.size≤T)
    (hG : 1≤G) (hT : T≤G) (hE : E≤f*G)
    (hW : (FixedLeadingTiltedSource.degree D).size≤W) (hD : FixedLeadingTiltedSource.degree D≤D')
    (ha : IntegralMixedExceptionalBounds.auxiliaryCap (n+2) (FixedLeadingTiltedSource.degree D)≤2^B)
    (c : IntegralMixedFullHistoryScript.Command
      (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) ((2:ℤ)^E)) B)
    (hc : IntegralMixedFullScriptHeight.CommandBounds ((f+2)*G+1) L c) :
    InstructionBounds G (f+2) W D' L
      (⟨FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) ((2:ℤ)^E),hcap,c⟩ : Instruction (n+1) B) where
  low e := (IntegralMixedCausalLevelLowHeight.tilted_source_coefficient u t ht hsize hG hT hE e).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))
  leading := by
    simp only [FermatLevelLift.source,FixedLeadingTiltedSource.source,Int.natAbs_one,Nat.size_one]
    omega
  width := hW
  degree := hD
  auxiliary := ha
  command := hc

theorem tilted_default_bounds {n k D T E f G B W D' L : ℕ} (u : Fin n) (t : ETR.Term)
    (ht : t.degreeBound≤D)
    (hcap : PurePowerReductionBounds.dimension (n+2) (FixedLeadingTiltedSource.degree D)≤2^B)
    (hsize : (FixedLeadingTiltedSource.lowTerm k D u.val t).toData.size≤T)
    (hG : 1≤G) (hT : T≤G) (hE : E≤f*G)
    (hW : (FixedLeadingTiltedSource.degree D).size≤W) (hD : FixedLeadingTiltedSource.degree D≤D')
    (ha : IntegralMixedExceptionalBounds.auxiliaryCap (n+2) (FixedLeadingTiltedSource.degree D)≤2^B) :
    InstructionBounds G (f+2) W D' L
      (⟨FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht) ((2:ℤ)^E),hcap,
        IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction (n+1) B) := by
  apply tilted_instruction_bounds u t ht hcap hsize hG hT hE hW hD ha
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact Nat.one_le_two_pow
  · exact Nat.zero_le _

end LeanCanny.Algebra.IntegralMixedFramedUnitSourceBounds
