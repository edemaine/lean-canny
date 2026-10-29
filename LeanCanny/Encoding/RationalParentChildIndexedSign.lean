/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildIndexedProbeSource
public import LeanCanny.Encoding.RationalParentChildTestSign

/-! # Native indexed polynomial signs at fixed regular-child descriptors

Input is `pair (pair source descriptor) queryIndex`. Only the test polynomial
receives the query index. The parameter, selected basis, hash parameters, and
descriptor validity all retain the original source context.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildIndexedSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open RationalParentChildTestMoments Brackets
open RationalParentChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
def testContext (q : List Bool) : List Bool := pair (origin q) (pairSnd q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

noncomputable def probeContext (P : Inputs) (q : List Bool) : List Bool :=
  pair (RationalParentChildHashChoice.value P (origin q))
    (pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
noncomputable def baseContext (P : Inputs) (q : List Bool) : List Bool :=
  RationalParentChildTestSign.probeContext P (pairFst q)

theorem probeContext_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (probeContext P) := by
  have H := (RationalParentChildHashChoice.evaluator h).precompose origin origin_FP
  have Q := SpaceFunction.ofFP (fun q => pair (SignedIntegerArithmetic.canonical (pairSnd (pairFst q))) (pairSnd q))
    (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) SignedIntegerArithmetic.canonical_FP) pairSnd_mem_FP)
  exact H.pairOutputs Q

theorem baseContext_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (baseContext P) :=
  (RationalParentChildTestSign.probeContext_evaluator h).precompose pairFst pairFst_mem_FP

theorem probeContext_packet (P : Inputs) (c d : List Bool) (z : ℤ) :
    probeContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      RationalParentChildIndexedProbeFrame.context P c z d := by
  simp only [probeContext, origin, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.canonical_eq,
    SignedIntegerArithmetic.value_packet, RationalParentChildIndexedProbeFrame.context]

theorem baseContext_packet (P : Inputs) (c d : List Bool) (z : ℤ) :
    baseContext P (pair (pair c (SignStatisticBits.integerCode z)) d) =
      RationalParentChildProbeSource.context P c z 0 := by
  rw [baseContext, pairFst_pair, RationalParentChildTestSign.probeContext_packet]

noncomputable def value (P : Inputs) (T : Test) (q : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (RationalParentChildIndexedProbe.firstCoefficient P T (probeContext P q)) *
      SignType.sign (RationalParentChildTestProbe.firstCoefficient P unit (baseContext P q)))

attribute [local irreducible] RationalParentChildIndexedProbe.firstCoefficient
  RationalParentChildTestProbe.firstCoefficient probeContext baseContext

theorem evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) : SpaceFunction (value P T) := by
  have L := (probeContext_evaluator h).chain (RationalParentChildIndexedProbe.sign_evaluator h A)
  have R := (baseContext_evaluator h).chain (RationalParentChildTestProbe.sign_evaluator h unitAccess)
  have E := (L.pairOutputs R).postcompose RationalParentChildTestSign.multiplyTags RationalParentChildTestSign.multiplyTags_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, RationalParentChildTestSign.multiplyTags_packet, value])

theorem value_root (P : Inputs) (T : Test) (c d : List Bool) (x : RationalParentChildRecordSpan.Root P c) :
    value P T (pair (pair c (SignStatisticBits.integerCode (RationalParentChildHashChoice.hash P c x))) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) := by
  rw [value, probeContext_packet, baseContext_packet, RationalParentChildIndexedProbeSource.pointwise]

theorem value_descriptor (P : Inputs) (T : Test) (c d : List Bool) (x : RationalParentChildRecordSpan.Root P c) :
    value P T (pair (pair c (RationalParentChildHashChoice.descriptor P c x)) d) =
      InfinitesimalSign.encode (sign T (pair c d) x.val) :=
  value_root P T c d x

theorem value_at (P : Inputs) (T : Test) (q : List Bool) (x : RationalParentChildRecordSpan.Root P (origin q))
    (hx : RationalParentChildHashChoice.descriptor P (origin q) x = pairSnd (pairFst q)) :
    value P T q = InfinitesimalSign.encode (sign T (testContext q) x.val) := by
  have hn : probeContext P q = probeContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [probeContext, origin, pairFst_pair, pairSnd_pair]
  have hd : baseContext P q = baseContext P (pair (pair (origin q) (pairSnd (pairFst q))) (pairSnd q)) := by
    simp only [baseContext, RationalParentChildTestSign.probeContext, origin, pairFst_pair, pairSnd_pair]
  rw [value, hn, hd, ← hx]
  exact value_descriptor P T (origin q) (pairSnd q) x

noncomputable def language (P : Inputs) (T : Test) (s : SignType) : Language :=
  {q | pairFst q ∈ RationalParentChildDescriptors.language P ∧ value P T q = InfinitesimalSign.encode s}

theorem decider {P : Inputs} (h : P.Access) {T : Test} (A : T.Access)
    (s : SignType) : SpaceDecider (language P T s) := by
  have V := ((RationalParentChildDescriptors.decider h).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (V.pairOutputs (evaluator h A)).decider (RationalParentChildTestSign.accept s) (RationalParentChildTestSign.accept_FP s)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, RationalParentChildTestSign.accept,
    pairFst_pair, pairSnd_pair, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Inputs} (h : P.Access) {T : Test} (A : T.Access)
    (s : SignType) : language P T s ∈ PSPACE :=
  (decider h A s).mem_PSPACE

theorem language_iff (P : Inputs) (T : Test) (s : SignType) (q : List Bool) : q ∈ language P T s ↔
    ∃ x : RationalParentChildRecordSpan.Root P (origin q),
      RationalParentChildHashChoice.descriptor P (origin q) x = pairSnd (pairFst q) ∧
        sign T (testContext q) x.val = s := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨x, hx⟩ := hv
    refine ⟨x, hx, ?_⟩
    rw [value_at P T q x hx] at hs
    exact (RationalParentChildTestSign.encode_eq_iff _ _).mp hs
  · rintro ⟨x, hx, hs⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P T q x hx, hs]

theorem language_invalid (P : Inputs) (T : Test) (s : SignType) (q : List Bool)
    (hq : pairFst q ∉ RationalParentChildDescriptors.language P) : q ∉ language P T s := fun h => hq h.1

noncomputable def ordinalQuery (P : Inputs) (q : List Bool) : List Bool :=
  pair (RationalParentChildTestSign.ordinalQuery P (pairFst q)) (pairSnd q)

theorem ordinalQuery_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (ordinalQuery P) :=
  ((RationalParentChildTestSign.ordinalQuery_evaluator h).precompose pairFst pairFst_mem_FP).pairOutputs
    (SpaceFunction.ofFP _ pairSnd_mem_FP)

noncomputable def atOrdinal (P : Inputs) (T : Test) (q : List Bool) : List Bool := value P T (ordinalQuery P q)
theorem ordinal_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) : SpaceFunction (atOrdinal P T) :=
  (ordinalQuery_evaluator h).chain (evaluator h A)

theorem ordinalQuery_packet (P : Inputs) (c d : List Bool) (r : Fin (RationalParentChildRegularCount.count P c)) :
    ordinalQuery P (pair (pair c (BinaryNatCode.encode r.val)) d) =
      pair (pair c (RationalParentChildHashChoice.descriptor P c (RationalParentChildHashEnumeration.root P c r))) d := by
  simp only [ordinalQuery, RationalParentChildTestSign.ordinalQuery, pairFst_pair, pairSnd_pair,
    RationalParentChildHashEnumeration.descriptor_root]

theorem ordinal_packet (P : Inputs) (T : Test) (c d : List Bool) (r : Fin (RationalParentChildRegularCount.count P c)) :
    atOrdinal P T (pair (pair c (BinaryNatCode.encode r.val)) d) =
      InfinitesimalSign.encode (sign T (pair c d) (RationalParentChildHashEnumeration.root P c r).val) := by
  have H := value_root P T c d (RationalParentChildHashEnumeration.root P c r)
  rw [RationalParentChildHashEnumeration.hash_root] at H
  simpa only [atOrdinal, ordinalQuery, RationalParentChildTestSign.ordinalQuery, pairFst_pair, pairSnd_pair] using H

end LeanCanny.Encoding.RationalParentChildIndexedSign
