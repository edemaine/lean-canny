/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixPoint
public import LeanCanny.Encoding.IntegralFramedTerminalCutReadback

/-! # Full chronological coefficient tests use one actual older homomorphism -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralFramedPhysicalBankTerm (input)
open IntegralFramedPhysicalSuffixTest (rawTuple)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def parent (B : Bank) (c u : List Bool) :=
  IntegralFramedTraceCutTask.task B.parameters (pair (pairFst c) (pair u []))
def datum (u : List Bool) (e k : ℕ) :=pair u (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))

theorem reindex_packet (B : Bank) (c u : List Bool) (e k : ℕ) :
    reindex B (pair c (datum u e k))=
      pair (parent B c u) (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) :=by
  simp only [reindex,datum,parent,IntegralFramedTraceCutTask.reindex,IntegralFramedTraceCutTask.selectors,
    pairFst_pair,pairSnd_pair]
  rw [IntegralFramedTraceCutTask.task_selectors B.parameters (pairFst c) u
    (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k)) []]

variable (B : Bank) (hkey : ∀c,B.key c=B.key (pair (pairFst c) []))
  (hFpos : ∀root,1≤B.factor root)
  (hf : ∀q,IntegralMixedFramedOriginalBounds.FallbackBounds B.parameters B.plan B.data B.nodes B.seed q)
  (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
  (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid (input B) c w)

theorem packet_fields (d p selectors : List Bool)
    (hp : pairFst (reindex B (pair c d))=p) (hs : pairSnd (reindex B (pair c d))=selectors) :
    value B hkey hFpos hf T hr (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((oldSource B hFpos hf).polynomial p selectors).eval₂ (Int.castRingHom ℝ)
        (fun i=>rawTuple B c w hv ((oldSource B hFpos hf).newer p selectors+i.val)))) :=by
  cases hp
  cases hs
  exact IntegralFramedPhysicalSuffixTest.packet_raw B T hr (source B hkey hFpos hf) c w d hv

attribute [local irreducible] family oldSource rawTuple parent

variable (u : List Bool)
local notation "p" => parent B c u
local notation "G" => family B.parameters B.plan B.data
local notation "old" => IntegralMixedVirtualTaskBits.saved B.parameters p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "offset" => IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p-IntegralMixedCutSource.Family.birth G old

theorem evaluation (ha : IntegralMixedFramedFullCutProbeBits.Active B.parameters p)
    (hfit : (G).birth old≤IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p)
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=rawTuple B c w hv (i.val+offset)^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
        (2^(G).width old) ((G).birth old) i)
    (e k : ℕ) (he : e≤2^B.parameters.width (RankedHistoryTask.root p))
    (hk : k≤2^B.parameters.width (RankedHistoryTask.root p)) :
    value B hkey hFpos hf T hr (pair (pair c w) (datum u e k))=InfinitesimalSign.encode
      (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x bound rule
        (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e))) :=by
  have HC : pairFst (reindex B (pair c (datum u e k)))=p :=by
    rw [reindex_packet,pairFst_pair]
  have HS : pairSnd (reindex B (pair c (datum u e k)))=
      pair (BinaryNatCode.encode e) (BinaryNatCode.encode k) :=by
    rw [reindex_packet,pairSnd_pair]
  rw [packet_fields B hkey hFpos hf T hr c w hv (datum u e k) p _ HC HS]
  apply congrArg (fun v : ℝ=>InfinitesimalSign.encode (SignType.sign v))
  have HH : ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=rawTuple B c w hv
      (i.val+(IntegralFramedTerminalCutTest.count B.parameters B.plan B.data (taskKey B) p-
        IntegralFramedTerminalCutTest.arity B.parameters B.plan B.data (taskKey B) p
          (pair (BinaryNatCode.encode e) (BinaryNatCode.encode k))))^
      UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon B.parameters p)
        (2^(G).width old) ((G).birth old) i :=by
    simpa only [IntegralFramedTerminalCutTest.arity,IntegralFramedTerminalCutTest.oldArity_parent,
      Nat.min_eq_left hfit] using hφ
  have HE:=IntegralFramedTerminalCutTest.polynomial_evaluation B.parameters B.plan B.data (taskKey B) p e k
    ha he hk (by rw [IntegralFramedTerminalCutTest.oldArity_parent];exact hfit) (rawTuple B c w hv) φ HH
  unfold oldSource
  simp only [IntegralFramedTerminalCutTest.source]
  simpa only [Nat.add_comm] using HE

end LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
