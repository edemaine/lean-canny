/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildIndexedProbeSource
public import LeanCanny.Encoding.BoundedFullSampleChildTestSign

/-! # Native indexed polynomial signs at fixed regular-child descriptors

Input is `pair (pair source descriptor) queryIndex`. Only the test polynomial
receives the query index. The parameter, selected basis, hash parameters, and
descriptor validity all retain the original source context.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildIndexedSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedFullSampleChildTestMoments Brackets
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def testContext (q : List Bool) : List Bool := pair (origin q) (pairSnd q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def probeContext (P : Inputs) (q : List Bool) : List Bool :=
  pair (BoundedFullSampleChildHashChoice.value P (origin q))
    (pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
noncomputable def baseContext (P : Inputs) (q : List Bool) : List Bool :=
  BoundedFullSampleChildTestSign.probeContext P (pairFst q)

theorem probeContext_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (probeContext P) := by
  have H := (BoundedFullSampleChildHashChoice.evaluator h).precompose origin origin_FP
  have Q := SpaceFunction.ofFP (fun q => pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) SignedIntegerArithmetic.canonical_FP) pairSnd_mem_FP)
  exact H.pairOutputs Q

theorem baseContext_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (baseContext P) :=
  (BoundedFullSampleChildTestSign.probeContext_evaluator h).precompose pairFst pairFst_mem_FP

theorem probeContext_packet (P : Inputs) (c d : List Bool) (z : ℤ) :
    probeContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      BoundedFullSampleChildIndexedProbeFrame.context P c z d := by
  simp only [probeContext, origin, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.canonical_eq,
    SignedIntegerArithmetic.value_packet, BoundedFullSampleChildIndexedProbeFrame.context]

theorem baseContext_packet (P : Inputs) (c d : List Bool) (z : ℤ) :
    baseContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      BoundedFullSampleChildProbeSource.context P c z 0 := by
  rw [baseContext, pairFst_pair, BoundedFullSampleChildTestSign.probeContext_packet]

noncomputable def value (P : Inputs) (T : Test) (q : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (BoundedFullSampleChildIndexedProbe.firstCoefficient P T (probeContext P q)) *
      SignType.sign (BoundedFullSampleChildTestProbe.firstCoefficient P unit (baseContext P q)))

attribute [local irreducible] BoundedFullSampleChildIndexedProbe.firstCoefficient
  BoundedFullSampleChildTestProbe.firstCoefficient probeContext baseContext

theorem evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) : SpaceFunction (value P T) := by
  have L := (probeContext_evaluator h).chain (BoundedFullSampleChildIndexedProbe.sign_evaluator h A)
  have R := (baseContext_evaluator h).chain (BoundedFullSampleChildTestProbe.sign_evaluator h unitAccess)
  have E := (L.pairOutputs R).postcompose BoundedFullSampleChildTestSign.multiplyTags BoundedFullSampleChildTestSign.multiplyTags_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, BoundedFullSampleChildTestSign.multiplyTags_packet, value])

theorem value_root (P : Inputs) (T : Test) (c d : List Bool) (x : BoundedFullSampleChildRecordSpan.Root P c) :
    value P T (pair (pair c (SignStatisticBits.integerCode (BoundedFullSampleChildHashChoice.hash P c x))) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) := by
  rw [value, probeContext_packet, baseContext_packet, BoundedFullSampleChildIndexedProbeSource.pointwise]

theorem value_descriptor (P : Inputs) (T : Test) (c d : List Bool) (x : BoundedFullSampleChildRecordSpan.Root P c) :
    value P T (pair (pair c (BoundedFullSampleChildHashChoice.descriptor P c x)) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) :=
  value_root P T c d x

theorem value_at (P : Inputs) (T : Test) (q : List Bool) (x : BoundedFullSampleChildRecordSpan.Root P (origin q))
    (hx : BoundedFullSampleChildHashChoice.descriptor P (origin q) x = pairSnd (pairFst q)) :
    value P T q = InfinitesimalSign.encode (sign T (testContext q) x.val) := by
  have hn : probeContext P q = probeContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [probeContext, origin, pairFst_pair, pairSnd_pair]
  have hd : baseContext P q = baseContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [baseContext, BoundedFullSampleChildTestSign.probeContext, origin, pairFst_pair, pairSnd_pair]
  rw [value, hn, hd, ← hx]
  exact value_descriptor P T (origin q) (pairSnd q) x

noncomputable def language (P : Inputs) (T : Test) (s : SignType) : Language :=
  {q | pairFst q ∈ BoundedFullSampleChildDescriptors.language P ∧ value P T q = InfinitesimalSign.encode s}

theorem decider {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access)
    (s : SignType) : SpaceDecider (language P T s) := by
  have V := ((BoundedFullSampleChildDescriptors.decider h).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (V.pairOutputs (evaluator h A)).decider (BoundedFullSampleChildTestSign.accept s) (BoundedFullSampleChildTestSign.accept_FP s)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, BoundedFullSampleChildTestSign.accept,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access)
    (s : SignType) : language P T s ∈ PSPACE :=
  (decider h A s).mem_PSPACE

theorem language_iff (P : Inputs) (T : Test) (s : SignType) (q : List Bool) : q ∈ language P T s ↔
    ∃ x : BoundedFullSampleChildRecordSpan.Root P (origin q),
      BoundedFullSampleChildHashChoice.descriptor P (origin q) x = pairSnd (pairFst q) ∧
        sign T (testContext q) x.val = s := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨x, hx⟩ := hv
    refine ⟨x, hx, ?_⟩
    rw [value_at P T q x hx] at hs
    exact (BoundedFullSampleChildTestSign.encode_eq_iff _ _).mp hs
  · rintro ⟨x, hx, hs⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P T q x hx, hs]

theorem language_invalid (P : Inputs) (T : Test) (s : SignType) (q : List Bool)
    (hq : pairFst q ∉ BoundedFullSampleChildDescriptors.language P) : q ∉ language P T s := fun h => hq h.1

noncomputable def ordinalQuery (P : Inputs) (q : List Bool) : List Bool :=
  pair (BoundedFullSampleChildTestSign.ordinalQuery P (pairFst q)) (pairSnd q)

theorem ordinalQuery_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (ordinalQuery P) :=
  ((BoundedFullSampleChildTestSign.ordinalQuery_evaluator h).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)

noncomputable def atOrdinal (P : Inputs) (T : Test) (q : List Bool) : List Bool := value P T (ordinalQuery P q)
theorem ordinal_evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) : SpaceFunction (atOrdinal P T) :=
  (ordinalQuery_evaluator h).chain (evaluator h A)

theorem ordinalQuery_packet (P : Inputs) (c d : List Bool) (r : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    ordinalQuery P (pair (pair c (BinaryNatCode.encode r.val)) d) =
      pair (pair c (BoundedFullSampleChildHashChoice.descriptor P c (BoundedFullSampleChildHashEnumeration.root P c r))) d := by
  simp only [ordinalQuery, BoundedFullSampleChildTestSign.ordinalQuery, pairFst_pair, pairSnd_pair,
    BoundedFullSampleChildHashEnumeration.descriptor_root]

theorem ordinal_packet (P : Inputs) (T : Test) (c d : List Bool) (r : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    atOrdinal P T (pair (pair c (BinaryNatCode.encode r.val)) d) =
      InfinitesimalSign.encode (sign T (pair c d) (BoundedFullSampleChildHashEnumeration.root P c r).val) := by
  have H := value_root P T c d (BoundedFullSampleChildHashEnumeration.root P c r)
  rw [BoundedFullSampleChildHashEnumeration.hash_root] at H
  simpa only [atOrdinal, ordinalQuery, BoundedFullSampleChildTestSign.ordinalQuery, pairFst_pair, pairSnd_pair] using H

end LeanCanny.Encoding.BoundedFullSampleChildIndexedSign
