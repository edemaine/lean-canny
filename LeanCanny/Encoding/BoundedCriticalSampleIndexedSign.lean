/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleIndexedProbeSource
public import LeanCanny.Encoding.BoundedCriticalSampleTestSign

/-! # Native indexed polynomial signs at fixed actual-sample descriptors

Input is `pair (pair source descriptor) queryIndex`. Only the test polynomial
receives the query index. The parameter, selected basis, hash parameters, and
descriptor validity all retain the original source context.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleIndexedSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleTestMoments Brackets
open scoped Classical

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def testContext (q : List Bool) : List Bool := pair (origin q) (pairSnd q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def probeContext (P : Readers) (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleHashChoice.value P (origin q))
    (pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
noncomputable def baseContext (P : Readers) (q : List Bool) : List Bool :=
  BoundedCriticalSampleTestSign.probeContext P (pairFst q)

theorem probeContext_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (probeContext P) := by
  have H := (BoundedCriticalSampleHashChoice.evaluator h ha).precompose origin origin_FP
  have Q := SpaceFunction.ofFP (fun q => pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) SignedIntegerArithmetic.canonical_FP) pairSnd_mem_FP)
  exact H.pairOutputs Q

theorem baseContext_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (baseContext P) :=
  (BoundedCriticalSampleTestSign.probeContext_evaluator h ha).precompose pairFst pairFst_mem_FP

theorem probeContext_packet (P : Readers) (c d : List Bool) (z : ℤ) :
    probeContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      BoundedCriticalSampleIndexedProbeFrame.context P c z d := by
  simp only [probeContext, origin, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.canonical_eq,
    SignedIntegerArithmetic.value_packet, BoundedCriticalSampleIndexedProbeFrame.context]

theorem baseContext_packet (P : Readers) (c d : List Bool) (z : ℤ) :
    baseContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      BoundedCriticalSampleProbeSource.context P c z 0 := by
  rw [baseContext, pairFst_pair, BoundedCriticalSampleTestSign.probeContext_packet]

noncomputable def value (P : Readers) (T : Test) (q : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (BoundedCriticalSampleIndexedProbe.firstCoefficient P T (probeContext P q)) *
      SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P unit (baseContext P q)))

attribute [local irreducible] BoundedCriticalSampleIndexedProbe.firstCoefficient
  BoundedCriticalSampleTestProbe.firstCoefficient probeContext baseContext

theorem evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P T) := by
  have L := (probeContext_evaluator h ha).chain (BoundedCriticalSampleIndexedProbe.sign_evaluator h A ha)
  have R := (baseContext_evaluator h ha).chain (BoundedCriticalSampleTestProbe.sign_evaluator h unitAccess ha)
  have E := (L.pairOutputs R).postcompose BoundedCriticalSampleTestSign.multiplyTags BoundedCriticalSampleTestSign.multiplyTags_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, BoundedCriticalSampleTestSign.multiplyTags_packet, value])

theorem value_root (P : Readers) (T : Test) (c d : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    value P T (pair (pair c (SignStatisticBits.integerCode (BoundedCriticalSampleHashChoice.hash P c x))) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) := by
  rw [value, probeContext_packet, baseContext_packet, BoundedCriticalSampleIndexedProbeSource.pointwise]

theorem value_sample (P : Readers) (T : Test) (c d : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    value P T (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) d) =
      InfinitesimalSign.encode (sign T (pair c d) (BoundedCriticalSampleLabels.parameter P c x).val) :=
  value_root P T c d (BoundedCriticalSampleLabels.parameter P c x)

theorem value_at (P : Readers) (T : Test) (q : List Bool) (x : BoundedFullCriticalSamples.Samples P (origin q))
    (hx : BoundedCriticalSampleHashChoice.descriptor P (origin q) x = pairSnd (pairFst q)) :
    value P T q = InfinitesimalSign.encode (sign T (testContext q) (BoundedCriticalSampleLabels.parameter P (origin q) x).val) := by
  have hn : probeContext P q = probeContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [probeContext, origin, pairFst_pair, pairSnd_pair]
  have hd : baseContext P q = baseContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [baseContext, BoundedCriticalSampleTestSign.probeContext, origin, pairFst_pair, pairSnd_pair]
  rw [value, hn, hd, ← hx]
  exact value_sample P T (origin q) (pairSnd q) x

noncomputable def language (P : Readers) (T : Test) (s : SignType) : Language :=
  {q | pairFst q ∈ BoundedCriticalSampleDescriptors.language P ∧ value P T q = InfinitesimalSign.encode s}

theorem decider {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (language P T s) := by
  have V := ((BoundedCriticalSampleDescriptors.decider h ha).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (V.pairOutputs (evaluator h A ha)).decider (BoundedCriticalSampleTestSign.accept s) (BoundedCriticalSampleTestSign.accept_FP s)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, BoundedCriticalSampleTestSign.accept,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : language P T s ∈ PSPACE :=
  (decider h A ha s).mem_PSPACE

theorem language_iff (P : Readers) (T : Test) (s : SignType) (q : List Bool) : q ∈ language P T s ↔
    ∃ x : BoundedFullCriticalSamples.Samples P (origin q),
      BoundedCriticalSampleHashChoice.descriptor P (origin q) x = pairSnd (pairFst q) ∧
        sign T (testContext q) (BoundedCriticalSampleLabels.parameter P (origin q) x).val = s := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨x, hx⟩ := hv
    refine ⟨x, hx, ?_⟩
    rw [value_at P T q x hx] at hs
    exact (BoundedCriticalSampleTestSign.encode_eq_iff _ _).mp hs
  · rintro ⟨x, hx, hs⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P T q x hx, hs]

theorem language_invalid (P : Readers) (T : Test) (s : SignType) (q : List Bool)
    (hq : pairFst q ∉ BoundedCriticalSampleDescriptors.language P) : q ∉ language P T s := fun h => hq h.1

noncomputable def ordinalQuery (P : Readers) (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleTestSign.ordinalQuery P (pairFst q)) (pairSnd q)

theorem ordinalQuery_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (ordinalQuery P) :=
  ((BoundedCriticalSampleTestSign.ordinalQuery_evaluator h ha).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)

noncomputable def atOrdinal (P : Readers) (T : Test) (q : List Bool) : List Bool := value P T (ordinalQuery P q)
theorem ordinal_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (atOrdinal P T) :=
  (ordinalQuery_evaluator h ha).chain (evaluator h A ha)

theorem ordinalQuery_packet (P : Readers) (c d : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    ordinalQuery P (pair (pair c (BinaryNatCode.encode r.val)) d) =
      pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c (BoundedCriticalSampleHashEnumeration.sampleEquiv P c r))) d := by
  simp only [ordinalQuery, BoundedCriticalSampleTestSign.ordinalQuery, pairFst_pair, pairSnd_pair,
    BoundedCriticalSampleHashEnumeration.descriptor_sample]

theorem ordinal_packet (P : Readers) (T : Test) (c d : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    atOrdinal P T (pair (pair c (BinaryNatCode.encode r.val)) d) =
      InfinitesimalSign.encode (sign T (pair c d) (BoundedCriticalSampleHashEnumeration.root P c r).val) := by
  have H := value_root P T c d (BoundedCriticalSampleHashEnumeration.root P c r)
  rw [BoundedCriticalSampleHashEnumeration.hash_root] at H
  simpa only [atOrdinal, ordinalQuery, BoundedCriticalSampleTestSign.ordinalQuery, pairFst_pair, pairSnd_pair] using H

end LeanCanny.Encoding.BoundedCriticalSampleIndexedSign
