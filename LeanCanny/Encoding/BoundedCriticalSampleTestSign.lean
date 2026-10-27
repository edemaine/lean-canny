/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTestProbeSource
public import LeanCanny.Encoding.BoundedCriticalSampleDescriptors
public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Native polynomial signs at actual-sample descriptors

The point word is the canonical signed descriptor of one actual full critical
sample. Parameter selection, filtered basis moments, and both determinant
coefficient signs are computed internally. The guarded language rejects
invalid descriptor words. Hash-order ordinals also have a native sign reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTestSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleTestMoments Brackets
open scoped Classical

noncomputable def probeContext (P : Readers) (u : List Bool) : List Bool :=
  pair (BoundedCriticalSampleHashChoice.value P (pairFst u))
    (pair (SignedIntegerArithmetic.canonical (pairSnd u)) [])

theorem probeContext_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (probeContext P) := by
  have H := (BoundedCriticalSampleHashChoice.evaluator h ha).precompose pairFst pairFst_mem_FP
  have Q := SpaceFunction.ofFP (fun u => pair (SignedIntegerArithmetic.canonical (pairSnd u)) [])
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP SignedIntegerArithmetic.canonical_FP) (constFn_mem_FP []))
  exact H.pairOutputs Q

theorem probeContext_packet (P : Readers) (c : List Bool) (z : ℤ) :
    probeContext P (pair c (SignStatisticBits.integerCode z)) = BoundedCriticalSampleProbeSource.context P c z 0 := by
  simp only [probeContext, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.canonical_eq,
    SignedIntegerArithmetic.value_packet, BoundedCriticalSampleProbeSource.context,
    BoundedCriticalSampleProbeEntries.context]
  rfl

def multiplyTags (z : List Bool) : List Bool :=
  if pairFst z = [] ∨ pairSnd z = [] then []
  else if pairFst z = pairSnd z then [false, true] else [true]

theorem multiplyTags_FP : multiplyTags ∈ FP := by
  have hz := (stringEq_fppred pairFst_mem_FP (constFn_mem_FP [])).or
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP []))
  have he := (stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).ite_mem_FP
    (constFn_mem_FP [false, true]) (constFn_mem_FP [true])
  exact hz.ite_mem_FP (constFn_mem_FP []) he

theorem multiplyTags_packet (a b : SignType) :
    multiplyTags (pair (InfinitesimalSign.encode a) (InfinitesimalSign.encode b)) =
      InfinitesimalSign.encode (a * b) := by
  cases a <;> cases b <;> decide

noncomputable def value (P : Readers) (T : Test) (u : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P T (probeContext P u)) *
      SignType.sign (BoundedCriticalSampleTestProbe.firstCoefficient P unit (probeContext P u)))

attribute [local irreducible] BoundedCriticalSampleTestProbe.firstCoefficient probeContext

theorem evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P T) := by
  have D := probeContext_evaluator h ha
  have L := D.chain (BoundedCriticalSampleTestProbe.sign_evaluator h A ha)
  have R := D.chain (BoundedCriticalSampleTestProbe.sign_evaluator h unitAccess ha)
  have E := (L.pairOutputs R).postcompose multiplyTags multiplyTags_FP
  exact E.congr (funext fun u => by simp only [Function.comp_apply, multiplyTags_packet, value])

theorem value_root (P : Readers) (T : Test) (c : List Bool) (x : BoundedCriticalSampleRecordSpan.Root P c) :
    value P T (pair c (SignStatisticBits.integerCode (BoundedCriticalSampleHashChoice.hash P c x))) =
      InfinitesimalSign.encode (sign T c x.val) := by
  rw [value, probeContext_packet, BoundedCriticalSampleTestProbeSource.pointwise]

theorem value_sample (P : Readers) (T : Test) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    value P T (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) =
      InfinitesimalSign.encode (sign T c (BoundedCriticalSampleLabels.parameter P c x).val) :=
  value_root P T c (BoundedCriticalSampleLabels.parameter P c x)

theorem value_at (P : Readers) (T : Test) (q : List Bool) (x : BoundedFullCriticalSamples.Samples P (pairFst q))
    (hx : BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q) :
    value P T q = InfinitesimalSign.encode (sign T (pairFst q) (BoundedCriticalSampleLabels.parameter P (pairFst q) x).val) := by
  have he : probeContext P q = probeContext P (pair (pairFst q) (pairSnd q)) := by
    simp only [probeContext, pairFst_pair, pairSnd_pair]
  rw [value, he, ← hx]
  exact value_sample P T (pairFst q) x

noncomputable def language (P : Readers) (T : Test) (s : SignType) : Language :=
  {u | u ∈ BoundedCriticalSampleDescriptors.language P ∧ value P T u = InfinitesimalSign.encode s}

def accept (s : SignType) (z : List Bool) : Bool := decide
  (pairFst z = [true] ∧ pairSnd z = InfinitesimalSign.encode s)

theorem accept_FP (s : SignType) : (fun z => [accept s z]) ∈ FP :=
  ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP (InfinitesimalSign.encode s)))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (language P T s) := by
  have V := (BoundedCriticalSampleDescriptors.decider h ha).flagEvaluator
  apply (V.pairOutputs (evaluator h A ha)).decider (accept s) (accept_FP s)
  intro u
  simp only [language, Set.mem_ofPred_eq, accept, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : language P T s ∈ PSPACE :=
  (decider h A ha s).mem_PSPACE

theorem encode_eq_iff (a b : SignType) : InfinitesimalSign.encode a = InfinitesimalSign.encode b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem language_iff (P : Readers) (T : Test) (s : SignType) (q : List Bool) : q ∈ language P T s ↔
    ∃ x : BoundedFullCriticalSamples.Samples P (pairFst q),
      BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q ∧
        sign T (pairFst q) (BoundedCriticalSampleLabels.parameter P (pairFst q) x).val = s := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨x, hx⟩ := hv
    refine ⟨x, hx, ?_⟩
    rw [value_at P T q x hx] at hs
    exact (encode_eq_iff _ _).mp hs
  · rintro ⟨x, hx, hs⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P T q x hx, hs]

theorem language_invalid (P : Readers) (T : Test) (s : SignType) (q : List Bool)
    (hq : q ∉ BoundedCriticalSampleDescriptors.language P) : q ∉ language P T s := fun h => hq h.1

noncomputable def ordinalQuery (P : Readers) (u : List Bool) : List Bool :=
  pair (pairFst u) (SignStatisticBits.integerCode (BoundedCriticalSampleHashEnumeration.value P u))

def ordinalFinish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
theorem ordinalFinish_FP : ordinalFinish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem ordinalQuery_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (ordinalQuery P) := by
  have E := (BoundedCriticalSampleHashEnumeration.evaluator h ha).withInput.postcompose ordinalFinish ordinalFinish_FP
  exact E.congr (funext fun u => by simp only [ordinalQuery, ordinalFinish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def atOrdinal (P : Readers) (T : Test) (u : List Bool) : List Bool := value P T (ordinalQuery P u)

theorem ordinal_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (atOrdinal P T) :=
  (ordinalQuery_evaluator h ha).chain (evaluator h A ha)

theorem ordinal_packet (P : Readers) (T : Test) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c)) :
    atOrdinal P T (pair c (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (sign T c (BoundedCriticalSampleHashEnumeration.root P c r).val) := by
  have H := value_root P T c (BoundedCriticalSampleHashEnumeration.root P c r)
  rw [BoundedCriticalSampleHashEnumeration.hash_root] at H
  simpa only [atOrdinal, ordinalQuery, pairFst_pair] using H

noncomputable def ordinalLanguage (P : Readers) (T : Test) (s : SignType) : Language :=
  {u | Nat.fromBitsLE (pairSnd u) < BoundedCriticalSampleCount.count P (pairFst u) ∧
    atOrdinal P T u = InfinitesimalSign.encode s}

def ordinalAccept (s : SignType) (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    pairSnd (pairSnd z) = InfinitesimalSign.encode s)

theorem ordinalAccept_FP (s : SignType) : (fun z => [ordinalAccept s z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  exact ((hi.lt hN).and (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (constFn_mem_FP (InfinitesimalSign.encode s)))).flag_mem_FP

theorem ordinal_decider {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (ordinalLanguage P T s) := by
  have N := (BoundedCriticalSampleCount.evaluator h ha).precompose pairFst pairFst_mem_FP
  apply (N.pairOutputs (ordinal_evaluator h A ha)).withInput.decider (ordinalAccept s) (ordinalAccept_FP s)
  intro u
  simp only [ordinalLanguage, Set.mem_ofPred_eq, ordinalAccept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem ordinal_mem_PSPACE {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : ordinalLanguage P T s ∈ PSPACE :=
  (ordinal_decider h A ha s).mem_PSPACE

theorem ordinal_language_packet (P : Readers) (T : Test) (c : List Bool)
    (r : Fin (BoundedCriticalSampleCount.count P c)) (s : SignType) :
    pair c (BinaryNatCode.encode r.val) ∈ ordinalLanguage P T s ↔
      sign T c (BoundedCriticalSampleHashEnumeration.root P c r).val = s := by
  change _ ∧ atOrdinal P T _ = _ ↔ _
  rw [ordinal_packet]
  have hr : Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r.val))) <
      BoundedCriticalSampleCount.count P (pairFst (pair c (BinaryNatCode.encode r.val))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [and_iff_right hr, encode_eq_iff]

theorem ordinal_language_invalid (P : Readers) (T : Test) (s : SignType) (u : List Bool)
    (hu : BoundedCriticalSampleCount.count P (pairFst u) ≤ Nat.fromBitsLE (pairSnd u)) :
    u ∉ ordinalLanguage P T s := fun h => (Nat.not_lt_of_ge hu) h.1

noncomputable def parameterTest (P : Readers) : Test where
  polynomial := BoundedCriticalRationalCoordinates.parameter P
  degree := BoundedCriticalRationalCoordinates.parameterDegree P
  mass := BoundedCriticalRationalCoordinates.baseHeight P
  polynomial_degree c := (BoundedCriticalRationalCoordinates.parameter_bounds P c).1
  polynomial_mass c := (BoundedCriticalRationalCoordinates.parameter_bounds P c).2

noncomputable def parameterAccess {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : (parameterTest P).Access :=
  Test.Access.ofPrimitive (BoundedCriticalRationalCoordinates.parameterDegree_binary h)
    (BoundedCriticalRationalCoordinates.baseHeight_binary h)
    (BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha)

theorem parameter_value (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    value P (parameterTest P) (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) = [] := by
  rw [value_sample]
  have hr := ((BoundedCriticalSampleLabels.mem_rootSet P c _).mp (BoundedCriticalSampleLabels.parameter P c x).property).1
  simp only [sign, parameterTest, Polynomial.eval_map, hr, sign_zero, InfinitesimalSign.encode]

end LeanCanny.Encoding.BoundedCriticalSampleTestSign
