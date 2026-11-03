/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSuffixTest
public import LeanCanny.Encoding.IntegralFramedTraceCutSource

/-! # Chronological cut probes keep the original full physical sampler

The creating parent task is written only into polynomial metadata.
Its old raw suffix enters the actual full tuple through native scalar
columns. No scalar sampler vertex or evaluation is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (B : Bank)
  (hkey : ∀c,B.key c=B.key (pair (pairFst c) []))

def taskKey (c : List Bool) :=B.key (pair (RankedHistoryTask.root c) [])
theorem taskKey_FP (h : IntegralFramedBankQuery.Access B) : taskKey B∈FP :=
  mem_FP_comp (mem_FP_pair RankedHistoryTask.root_FP (constFn_mem_FP [])) h.key
theorem taskPositive (c : List Bool) : 0<(family B.parameters B.plan B.data).birth (taskKey B c) :=
  B.positive _

def reindex (z : List Bool) :=IntegralFramedTraceCutTask.reindex B.parameters
  (pair (pairFst (pairFst z)) (pairSnd z))
theorem reindex_FP (h : IntegralFramedBankQuery.Access B) : reindex B∈FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (IntegralFramedTraceCutTask.reindex_FP B.parameters h.parameters)

include hkey in
theorem count_eq (c d : List Bool) :
    (IntegralFramedCompleteSquare.input B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
      (taskKey B) (taskPositive B)).count (pairFst (reindex B (pair c d)))=
        (IntegralFramedBankQuery.input B).count c :=by
  change (family B.parameters B.plan B.data).birth (taskKey B (pairFst (reindex B (pair c d))))=
    (family B.parameters B.plan B.data).birth (B.key c)
  apply congrArg (family B.parameters B.plan B.data).birth
  unfold taskKey reindex IntegralFramedTraceCutTask.reindex
  rw [pairFst_pair,pairFst_pair,pairSnd_pair,IntegralFramedTraceCutTask.task_root,pairFst_pair]
  exact (hkey c).symm

variable (hFpos : ∀root,1≤B.factor root)
  (hf : ∀q,IntegralMixedFramedOriginalBounds.FallbackBounds B.parameters B.plan B.data B.nodes B.seed q)

noncomputable def oldSource :=IntegralFramedTerminalCutTest.source B.parameters B.plan B.data
  B.nodes B.factor B.seed B.bounds (taskKey B) (taskPositive B) hFpos hf
noncomputable def source : SquareSampleCompleteSuffixPolynomialTest.Source (IntegralFramedBankQuery.input B) :=
  (oldSource B hFpos hf).reindex (reindex B) (count_eq B hkey)

attribute [local irreducible] family oldSource

variable (h : IntegralFramedBankQuery.Access B)
  (ctl : IntegralMixedFramedCurrentQNativeBits.Controls
    (IntegralMixedFramedCutProbeTaskBits.parameters B.parameters B.nodes B.factor B.seed)
    (IntegralMixedFramedCutProbeTransportBits.plan B.parameters B.plan B.nodes B.factor B.seed)
    (IntegralMixedFramedCutProbeTransportBits.data B.parameters B.plan B.data B.nodes B.factor B.seed))
  (hb : IntegralMixedFramedCurrentQNativeBits.Bounds
    (IntegralMixedFramedCutProbeTaskBits.parameters B.parameters B.nodes B.factor B.seed)
    (IntegralMixedFramedCutProbeTransportBits.plan B.parameters B.plan B.nodes B.factor B.seed)
    (IntegralMixedFramedCutProbeTransportBits.data B.parameters B.plan B.data B.nodes B.factor B.seed) ctl)

include h ctl hb in
theorem source_access : (source B hkey hFpos hf).Access :=by
  unfold source oldSource
  exact (IntegralFramedTerminalCutTest.access B.parameters h.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
    h.nodes h.factor h.seed hFpos hf (taskKey B) (taskKey_FP B h) (taskPositive B) ctl hb).reindex
      (reindex B) (reindex_FP B h) (count_eq B hkey)

variable (T : IntegralMixedHeaderTablesBits.Tables)
  (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)

noncomputable def value :=IntegralFramedPhysicalSuffixTest.value B T hr (source B hkey hFpos hf)

include h ctl hb in
theorem evaluator (ht : IntegralMixedHeaderTablesBits.Access T)
    (ER : SpaceFunction (SquareSampleInput.rowCoefficient (IntegralFramedPhysicalBankTerm.input B))) :
    SpaceFunction (value B hkey hFpos hf T hr) :=
  IntegralFramedPhysicalSuffixTest.evaluator B T hr (source B hkey hFpos hf) h ht
    (source_access B hkey hFpos hf h ctl hb) ER

theorem packet (c w d : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w) :
    value B hkey hFpos hf T hr (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign (((source B hkey hFpos hf).polynomial c d).eval₂ (Int.castRingHom ℝ)
        (fun i=>(SquareSampleCompleteVertices.candidate (IntegralFramedPhysicalBankTerm.input B) c w hv).val
          (IntegralFramedPhysicalSuffixTest.columns B T hr (source B hkey hFpos hf) c d i)))) :=
  IntegralFramedPhysicalSuffixTest.packet B T hr (source B hkey hFpos hf) c w d hv

end LeanCanny.Encoding.IntegralFramedPhysicalTraceCutSource
