/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSemantics
public import LeanCanny.Encoding.IntegralFramedPhysicalOlderParent

/-! # The full tuple constructs its chronological cut parent's homomorphism -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open IntegralFramedPhysicalSuffixTest (rawTuple)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem extend_embed {n m : ℕ} (hfit : n≤m) (z : Fin m→ℝ) (i : Fin n) :
    IntegralMixedFramedBankObservation.extend z (i.val+(m-n))=
      z (UniformIntegralPowerSchedule.embed hfit i) :=by
  have HI : i.val+(m-n)<m :=by have HH:=i.isLt;omega
  unfold IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HI]
  apply congrArg z
  apply Fin.ext
  exact Nat.add_comm _ _

variable (B : Bank) (hkey : ∀c,B.key c=B.key (pair (pairFst c) []))
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w) (u : List Bool)
local notation "p" => parent B c u
local notation "G" => family B.parameters B.plan B.data
local notation "old" => IntegralMixedVirtualTaskBits.saved B.parameters p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "offset" => IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p-
  IntegralMixedCutSource.Family.birth G old

include hkey in
theorem taskKey_parent : taskKey B p=B.key c :=by
  unfold taskKey parent
  rw [IntegralFramedTraceCutTask.task_root,pairFst_pair]
  exact (hkey c).symm

theorem parent_root : pairFst old=pairFst c :=by
  rw [IntegralMixedFullHistoryFamilyBits.saved_root]
  unfold parent
  rw [IntegralFramedTraceCutTask.task_root,pairFst_pair]

theorem parent_horizon : (G).cap old=IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p :=by
  change B.parameters.cap (pairFst old)+1=B.parameters.cap (RankedHistoryTask.root p)+1
  rw [IntegralMixedFullHistoryFamilyBits.saved_root]

attribute [local irreducible] family rawTuple parent

include hkey in
theorem count_parent :
    IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p=(G).birth (B.key c) :=by
  unfold IntegralFramedTerminalCutTest.count
  rw [taskKey_parent B hkey c u]

include hkey in
theorem exists_parent_interpretation (hroot : pairFst (B.key c)=pairFst c)
    (hfit : (G).birth old≤(G).birth (B.key c)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=rawTuple B c w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
          (2^(G).width old) ((G).birth old) i :=by
  obtain ⟨φ,hφ⟩:=IntegralFramedPhysicalOlderParent.exists_interpretation
    B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv old
      (hroot.trans (parent_root B c u).symm) hfit
  refine ⟨φ,fun i=>?_⟩
  have HX : rawTuple B c w hv (i.val+offset)=
      IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hv (UniformIntegralPowerSchedule.embed hfit i) :=by
    rw [count_parent B hkey c u]
    unfold rawTuple
    exact extend_embed hfit _ i
  have HW:=congrArg (fun S : ℕ=>UniformIntegralPowerSchedule.weights S
    (2^(G).width old) ((G).birth old) i) (parent_horizon B c u)
  have HE:=congrArg (fun e : ℕ=>
    (IntegralFramedPhysicalSquare.scalarTuple B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
      B.key B.positive c w hv (UniformIntegralPowerSchedule.embed hfit i))^e) HW
  exact (hφ i).trans (HE.trans (congrArg (fun a : ℝ=>a^
    UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
      (2^(G).width old) ((G).birth old) i) HX.symm))

theorem exists_coefficient_evaluation
    (hFpos : ∀root,1≤B.factor root)
    (hf : ∀q,IntegralMixedFramedOriginalBounds.FallbackBounds B.parameters B.plan B.data B.nodes B.seed q)
    (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (hroot : pairFst (B.key c)=pairFst c)
    (hfit : (G).birth old≤(G).birth (B.key c))
    (ha : IntegralMixedFramedFullCutProbeBits.Active B.parameters p) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=rawTuple B c w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
          (2^(G).width old) ((G).birth old) i) ∧
      ∀e k,e≤2^B.parameters.width (RankedHistoryTask.root p)→k≤2^B.parameters.width (RankedHistoryTask.root p)→
        value B hkey hFpos hf T hr (pair (pair c w) (datum u e k))=InfinitesimalSign.encode
          (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x (IntegralMixedCutSource.Family.birth_bound G old)
            (IntegralMixedCutSource.Family.rule G old)
            (IntegralMixedRelativeCuts.atChoice (IntegralMixedCutSource.Family.rule G old)
              (IntegralMixedCutSource.Family.kind G old) k)).coeff e))) :=by
  obtain ⟨φ,hφ⟩:=exists_parent_interpretation B hkey c w hv u hroot hfit
  refine ⟨φ,hφ,fun e k he hk=>?_⟩
  exact evaluation B hkey hFpos hf T hr c w hv u ha
    (hfit.trans_eq (count_parent B hkey c u).symm) φ hφ e k he hk

end LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
