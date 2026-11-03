/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTraceCutOrigin
public import LeanCanny.Encoding.SquareSampleCompleteSuffixEvaluation
public import LeanCanny.Encoding.IntegralFramedTerminalCutReadback
public import LeanCanny.Encoding.IntegralFramedCompleteSuffix
/-! # Every datum-indexed cut coefficient specializes at the same joint tail -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTraceCutReadback
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralFramedTraceCutMetadata (terminal key terminal_positive key_positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (hFpos : ∀ root,1≤F root) (hf : ∀ q,IntegralMixedFramedOriginalBounds.FallbackBounds P D H L C q)
  (r u : List Bool)
local notation "c" => IntegralFramedTraceCutTask.task P (pair r (pair u []))
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "delta" => IntegralFramedTerminalCutTest.count P D H (key P D) c-IntegralMixedCutSource.Family.birth G parent
local notation "S" => IntegralFramedTraceCutSource.source P D H L F C hs hFpos hf

theorem evaluation (z : ℕ→ℝ) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hfit : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H (key P D) c)
    (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+delta)^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i)
    (e k : ℕ) (he : e≤2^P.width r) (hk : k≤2^P.width r) :
    (S).evaluation r (pair u (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))) z=
      φ ((IntegralMixedRelativeCuts.factor old bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e) := by
  let d:=pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)
  have HE:=SquareSampleCompleteSuffixPolynomialTest.Source.reindex_evaluation
    (IntegralFramedTraceCutSource.oldSource P D H L F C hs hFpos hf)
    (IntegralFramedTraceCutTask.reindex P) (IntegralFramedTraceCutSource.reindex_count P D H L F C hs) r (pair u d) z
  simp only [IntegralFramedTraceCutTask.reindex,pairFst_pair,pairSnd_pair,IntegralFramedTraceCutTask.selectors_packet] at HE
  rw [IntegralFramedTraceCutTask.task_selectors P r u d []] at HE
  refine HE.trans ?_
  apply IntegralFramedTerminalCutTest.polynomial_evaluation P D H (key P D) c e k ha
  · simpa only [IntegralFramedTraceCutTask.task_root,pairFst_pair] using he
  · simpa only [IntegralFramedTraceCutTask.task_root,pairFst_pair] using hk
  · rw [IntegralFramedTerminalCutTest.oldArity_parent]
    exact hfit
  · simpa only [IntegralFramedTerminalCutTest.arity,IntegralFramedTerminalCutTest.oldArity_parent,Nat.min_eq_left hfit] using hφ

variable (w : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (IntegralFramedTraceCutSource.input P D H L F C hs) r w)
local notation "z" => IntegralFramedCompleteSuffix.joint P D H L F C hs (terminal P D) (terminal_positive P D H) r w hv

include hv in
theorem packet (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hfit : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H (key P D) c)
    (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+delta)^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i)
    (e k : ℕ) (he : e≤2^P.width r) (hk : k≤2^P.width r) :
    IntegralFramedTraceCutSource.value P D H L F C hs hFpos hf
      (pair (pair r w) (pair u (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))))=
      InfinitesimalSign.encode (SignType.sign
        (φ ((IntegralMixedRelativeCuts.factor old bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e))) := by
  have HP:=SquareSampleCompleteSuffixPolynomialTest.packet_evaluation S r w
    (pair u (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))) hv
  have HE:=evaluation P D H L F C hs hFpos hf r u z ha hfit φ hφ e k he hk
  exact HP.trans (congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v)) HE)

include hv in
theorem zero_iff (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
    (hfit : (G).birth parent≤IntegralFramedTerminalCutTest.count P D H (key P D) c)
    (φ : (old).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀ i,φ ((old).sampler.scalarPrefix.basis.generator i)=z (i.val+delta)^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P c)
        (2^(G).width parent) ((G).birth parent) i)
    (e k : ℕ) (he : e≤2^P.width r) (hk : k≤2^P.width r) :
    FiniteCoefficientSignScan.Zero (IntegralFramedTraceCutGuards.sign P D H L F C hs hFpos hf) (pair (pair r w) u) e k ↔
      φ ((IntegralMixedRelativeCuts.factor old bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e)=0 := by
  unfold FiniteCoefficientSignScan.Zero FiniteCoefficientSignScan.query IntegralFramedTraceCutGuards.sign
  simp only [Function.comp_apply,IntegralFramedTraceCutGuards.signQuery,pairFst_pair,pairSnd_pair]
  rw [packet P D H L F C hs hFpos hf r u w hv ha hfit φ hφ e k he hk]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

end LeanCanny.Encoding.IntegralFramedTraceCutReadback
