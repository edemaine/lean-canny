/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildIndexedProbeSource
public import LeanCanny.Encoding.BoundedCriticalSampleChildTestSign

/-! # Native indexed polynomial signs at fixed regular-child descriptors

Input is `pair (pair source descriptor) queryIndex`. Only the test polynomial
receives the query index. The parameter, selected basis, hash parameters, and
descriptor validity all retain the original source context.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildIndexedSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleChildTestMoments Brackets
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def testContext (q : List Bool) : List Bool := pair (origin q) (pairSnd q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def probeContext (P : Inputs) (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleChildHashChoice.value P (origin q))
    (pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
noncomputable def baseContext (P : Inputs) (q : List Bool) : List Bool :=
  BoundedCriticalSampleChildTestSign.probeContext P (pairFst q)

theorem probeContext_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (probeContext P) := by
  have H := (BoundedCriticalSampleChildHashChoice.evaluator h).precompose origin origin_FP
  have Q := SpaceFunction.ofFP (fun q => pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) SignedIntegerArithmetic.canonical_FP) pairSnd_mem_FP)
  exact H.pairOutputs Q

theorem baseContext_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (baseContext P) :=
  (BoundedCriticalSampleChildTestSign.probeContext_evaluator h).precompose pairFst pairFst_mem_FP

theorem probeContext_packet (P : Inputs) (c d : List Bool) (z : ℤ) :
    probeContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      BoundedCriticalSampleChildIndexedProbeFrame.context P c z d := by
  simp only [probeContext, origin, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.canonical_eq,
    SignedIntegerArithmetic.value_packet, BoundedCriticalSampleChildIndexedProbeFrame.context]

theorem baseContext_packet (P : Inputs) (c d : List Bool) (z : ℤ) :
    baseContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      BoundedCriticalSampleChildProbeSource.context P c z 0 := by
  rw [baseContext, pairFst_pair, BoundedCriticalSampleChildTestSign.probeContext_packet]

noncomputable def value (P : Inputs) (T : Test) (q : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (BoundedCriticalSampleChildIndexedProbe.firstCoefficient P T (probeContext P q)) *
      SignType.sign (BoundedCriticalSampleChildTestProbe.firstCoefficient P unit (baseContext P q)))

attribute [local irreducible] BoundedCriticalSampleChildIndexedProbe.firstCoefficient
  BoundedCriticalSampleChildTestProbe.firstCoefficient probeContext baseContext

theorem evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) : SpaceFunction (value P T) := by
  have L := (probeContext_evaluator h).chain (BoundedCriticalSampleChildIndexedProbe.sign_evaluator h A)
  have R := (baseContext_evaluator h).chain (BoundedCriticalSampleChildTestProbe.sign_evaluator h unitAccess)
  have E := (L.pairOutputs R).postcompose BoundedCriticalSampleChildTestSign.multiplyTags BoundedCriticalSampleChildTestSign.multiplyTags_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, BoundedCriticalSampleChildTestSign.multiplyTags_packet, value])

theorem value_root (P : Inputs) (T : Test) (c d : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    value P T (pair (pair c (SignStatisticBits.integerCode (BoundedCriticalSampleChildHashChoice.hash P c x))) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) := by
  rw [value, probeContext_packet, baseContext_packet, BoundedCriticalSampleChildIndexedProbeSource.pointwise]

theorem value_descriptor (P : Inputs) (T : Test) (c d : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    value P T (pair (pair c (BoundedCriticalSampleChildHashChoice.descriptor P c x)) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) :=
  value_root P T c d x

theorem value_at (P : Inputs) (T : Test) (q : List Bool) (x : BoundedCriticalSampleChildRecordSpan.Root P (origin q))
    (hx : BoundedCriticalSampleChildHashChoice.descriptor P (origin q) x = pairSnd (pairFst q)) :
    value P T q = InfinitesimalSign.encode (sign T (testContext q) x.val) := by
  have hn : probeContext P q = probeContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [probeContext, origin, pairFst_pair, pairSnd_pair]
  have hd : baseContext P q = baseContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [baseContext, BoundedCriticalSampleChildTestSign.probeContext, origin, pairFst_pair, pairSnd_pair]
  rw [value, hn, hd, ← hx]
  exact value_descriptor P T (origin q) (pairSnd q) x

noncomputable def language (P : Inputs) (T : Test) (s : SignType) : Language :=
  {q | pairFst q ∈ BoundedCriticalSampleChildDescriptors.language P ∧ value P T q = InfinitesimalSign.encode s}

theorem decider {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access)
    (s : SignType) : SpaceDecider (language P T s) := by
  have V := ((BoundedCriticalSampleChildDescriptors.decider h).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (V.pairOutputs (evaluator h A)).decider (BoundedCriticalSampleChildTestSign.accept s) (BoundedCriticalSampleChildTestSign.accept_FP s)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, BoundedCriticalSampleChildTestSign.accept,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access)
    (s : SignType) : language P T s ∈ PSPACE :=
  (decider h A s).mem_PSPACE

theorem language_iff (P : Inputs) (T : Test) (s : SignType) (q : List Bool) : q ∈ language P T s ↔
    ∃ x : BoundedCriticalSampleChildRecordSpan.Root P (origin q),
      BoundedCriticalSampleChildHashChoice.descriptor P (origin q) x = pairSnd (pairFst q) ∧
        sign T (testContext q) x.val = s := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨x, hx⟩ := hv
    refine ⟨x, hx, ?_⟩
    rw [value_at P T q x hx] at hs
    exact (BoundedCriticalSampleChildTestSign.encode_eq_iff _ _).mp hs
  · rintro ⟨x, hx, hs⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P T q x hx, hs]

theorem language_invalid (P : Inputs) (T : Test) (s : SignType) (q : List Bool)
    (hq : pairFst q ∉ BoundedCriticalSampleChildDescriptors.language P) : q ∉ language P T s := fun h => hq h.1

noncomputable def ordinalQuery (P : Inputs) (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleChildTestSign.ordinalQuery P (pairFst q)) (pairSnd q)

theorem ordinalQuery_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (ordinalQuery P) :=
  ((BoundedCriticalSampleChildTestSign.ordinalQuery_evaluator h).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)

noncomputable def atOrdinal (P : Inputs) (T : Test) (q : List Bool) : List Bool := value P T (ordinalQuery P q)
theorem ordinal_evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) : SpaceFunction (atOrdinal P T) :=
  (ordinalQuery_evaluator h).chain (evaluator h A)

theorem ordinalQuery_packet (P : Inputs) (c d : List Bool) (r : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    ordinalQuery P (pair (pair c (BinaryNatCode.encode r.val)) d) =
      pair (pair c (BoundedCriticalSampleChildHashChoice.descriptor P c (BoundedCriticalSampleChildHashEnumeration.root P c r))) d := by
  simp only [ordinalQuery, BoundedCriticalSampleChildTestSign.ordinalQuery, pairFst_pair, pairSnd_pair,
    BoundedCriticalSampleChildHashEnumeration.descriptor_root]

theorem ordinal_packet (P : Inputs) (T : Test) (c d : List Bool) (r : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    atOrdinal P T (pair (pair c (BinaryNatCode.encode r.val)) d) =
      InfinitesimalSign.encode (sign T (pair c d) (BoundedCriticalSampleChildHashEnumeration.root P c r).val) := by
  have H := value_root P T c d (BoundedCriticalSampleChildHashEnumeration.root P c r)
  rw [BoundedCriticalSampleChildHashEnumeration.hash_root] at H
  simpa only [atOrdinal, ordinalQuery, BoundedCriticalSampleChildTestSign.ordinalQuery, pairFst_pair, pairSnd_pair] using H

end LeanCanny.Encoding.BoundedCriticalSampleChildIndexedSign
