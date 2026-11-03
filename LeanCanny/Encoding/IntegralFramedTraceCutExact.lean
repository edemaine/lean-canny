/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutGuardComplete
public import LeanCanny.Encoding.IntegralFramedTerminalCutRows
public import LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
public import LeanCanny.Algebra.IntegralMixedCutJointRootGuard
public import LeanCanny.Algebra.IntegralMixedCutHeadRootGuard
/-! # Exact cut compatibility at one fixed terminal vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutExact
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutMetadata (terminal key terminal_positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (r u w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) r w)
local notation "c" => IntegralFramedTraceCutTask.task P (pair r (pair u []))
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "factor" => IntegralMixedRelativeCuts.factor old bound rule kind
local notation "M" => IntegralMixedCutSource.Family.birth G (terminal P D r)
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv
local notation "cutTuple" => (fun i : Fin (IntegralMixedCutSource.Family.birth G parent+1)=>z (Fin.val i+(M-(birth P c+1))))
local notation "bankPoint" => IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState (IntegralMixedCutSource.Family.state G (terminal P D r))) z (M-birth P c-1)

omit hFpos hf in
noncomputable def Compatible : Prop :=
  ∃ φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
    (∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+(M-(G).birth parent))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i) ∧
    IntegralMixedRelativeCuts.Valid old bound rule φ kind ∧ ((factor).map φ.toRingHom).natDegree=degree ∧
    (factor).eval₂ φ.toRingHom bankPoint=0

include hv in
theorem compatible_iff (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hcut : IntegralFramedCreatingCut.ParentCut P D c) (hstage : birth P c=u.length) (hfit : birth P c<M) :
    Compatible P D H L F C hs r u w hv ↔
      IntegralFramedTraceCutGuards.Guards P D H L F C hs hFpos hf (pair (pair r w) u) := by
  constructor
  · rintro ⟨φ,hφ,hvalid,hd,hr⟩
    have HR : pairFst (terminal P D r)=RankedHistoryTask.root c := by
      simp only [IntegralFramedTraceCutMetadata.terminal_root,IntegralFramedTraceCutTask.task_root,pairFst_pair]
    rw [IntegralFramedTerminalCutBankPoint.point_eq P D H c (terminal P D r) ha hcut HR hfit z] at hr
    exact IntegralFramedTraceCutGuardComplete.guards P D H L F C hs hFpos hf r u w hv ha hstage hfit φ hφ hvalid hd hr
  · exact IntegralFramedTraceCutRoot.exists_root P D H L F C hs hFpos hf r u w hv ha hcut hstage hfit

end LeanCanny.Encoding.IntegralFramedTraceCutExact
