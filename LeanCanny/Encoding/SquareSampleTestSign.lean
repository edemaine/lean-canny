/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleTestProbeSource
public import LeanCanny.Encoding.SquareSampleDescriptors
public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Native polynomial signs at regular square-system descriptors

The point word is the canonical signed descriptor of one regular square-system root. Parameter selection, filtered basis moments, and both determinant
coefficient signs are computed internally. The guarded language rejects
invalid descriptor words. Hash-order ordinals also have a native sign reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleTestSign
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleTestMoments Brackets
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] SquareSampleRecords.length SquareSampleThom.labelWidth
  SquareSampleCoordinates.parameterDegree SquareSampleCoordinates.baseHeight
  SquareSampleQueries.roots SquareSampleRegularCount.count

noncomputable def probeContext (P : Inputs) (u : List Bool) : List Bool :=
  pair (SquareSampleHashChoice.value P (pairFst u))
    (pair (SignedIntegerArithmetic.canonical (pairSnd u)) [])

theorem probeContext_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (probeContext P) := by
  have H := (SquareSampleHashChoice.evaluator h).precompose pairFst pairFst_mem_FP
  have Q := SpaceFunction.ofFP (fun u => pair (SignedIntegerArithmetic.canonical (pairSnd u)) [])
    (mem_FP_pair (mem_FP_comp pairSnd_mem_FP SignedIntegerArithmetic.canonical_FP) (constFn_mem_FP []))
  exact H.pairOutputs Q

theorem probeContext_packet (P : Inputs) (c : List Bool) (z : ℤ) :
    probeContext P (pair c (SignStatisticBits.integerCode z)) = SquareSampleProbeSource.context P c z 0 := by
  simp only [probeContext, pairFst_pair, pairSnd_pair, SignedIntegerArithmetic.canonical_eq,
    SignedIntegerArithmetic.value_packet, SquareSampleProbeSource.context,
    SquareSampleProbeEntries.context]
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

noncomputable def value (P : Inputs) (T : Test) (u : List Bool) : List Bool :=
  InfinitesimalSign.encode
    (SignType.sign (SquareSampleTestProbe.firstCoefficient P T (probeContext P u)) *
      SignType.sign (SquareSampleTestProbe.firstCoefficient P unit (probeContext P u)))

attribute [local irreducible] SquareSampleTestProbe.firstCoefficient probeContext

theorem evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) : SpaceFunction (value P T) := by
  have D := probeContext_evaluator h
  have L := D.chain (SquareSampleTestProbe.sign_evaluator h A)
  have R := D.chain (SquareSampleTestProbe.sign_evaluator h unitAccess)
  have E := (L.pairOutputs R).postcompose multiplyTags multiplyTags_FP
  exact E.congr (funext fun u => by simp only [Function.comp_apply, multiplyTags_packet, value])

theorem value_root (P : Inputs) (T : Test) (c : List Bool) (x : SquareSampleRecordSpan.Root P c) :
    value P T (pair c (SignStatisticBits.integerCode (SquareSampleHashChoice.hash P c x))) =
      InfinitesimalSign.encode (sign T c x.val) := by
  rw [value, probeContext_packet, SquareSampleTestProbeSource.pointwise]

theorem value_descriptor (P : Inputs) (T : Test) (c : List Bool) (x : SquareSampleRecordSpan.Root P c) :
    value P T (pair c (SquareSampleHashChoice.descriptor P c x)) =
      InfinitesimalSign.encode (sign T c x.val) :=
  value_root P T c x

theorem value_at (P : Inputs) (T : Test) (q : List Bool) (x : SquareSampleRecordSpan.Root P (pairFst q))
    (hx : SquareSampleHashChoice.descriptor P (pairFst q) x = pairSnd q) :
    value P T q = InfinitesimalSign.encode (sign T (pairFst q) x.val) := by
  have he : probeContext P q = probeContext P (pair (pairFst q) (pairSnd q)) := by
    simp only [probeContext, pairFst_pair, pairSnd_pair]
  rw [value, he, ← hx]
  exact value_descriptor P T (pairFst q) x

noncomputable def language (P : Inputs) (T : Test) (s : SignType) : Language :=
  {u | u ∈ SquareSampleDescriptors.language P ∧ value P T u = InfinitesimalSign.encode s}

def accept (s : SignType) (z : List Bool) : Bool := decide
  (pairFst z = [true] ∧ pairSnd z = InfinitesimalSign.encode s)

theorem accept_FP (s : SignType) : (fun z => [accept s z]) ∈ FP :=
  ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP (InfinitesimalSign.encode s)))).flag_mem_FP

theorem decider {P : Inputs} (h : P.Access) {T : Test} (A : T.Access)
    (s : SignType) : SpaceDecider (language P T s) := by
  have V := (SquareSampleDescriptors.decider h).flagEvaluator
  apply (V.pairOutputs (evaluator h A)).decider (accept s) (accept_FP s)
  intro u
  simp only [language, Set.mem_ofPred_eq, accept, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Inputs} (h : P.Access) {T : Test} (A : T.Access)
    (s : SignType) : language P T s ∈ PSPACE :=
  (decider h A s).mem_PSPACE

theorem encode_eq_iff (a b : SignType) : InfinitesimalSign.encode a = InfinitesimalSign.encode b ↔ a = b := by
  cases a <;> cases b <;> decide

theorem language_iff (P : Inputs) (T : Test) (s : SignType) (q : List Bool) : q ∈ language P T s ↔
    ∃ x : SquareSampleRecordSpan.Root P (pairFst q),
      SquareSampleHashChoice.descriptor P (pairFst q) x = pairSnd q ∧
        sign T (pairFst q) x.val = s := by
  constructor
  · rintro ⟨hv, hs⟩
    obtain ⟨x, hx⟩ := hv
    refine ⟨x, hx, ?_⟩
    rw [value_at P T q x hx] at hs
    exact (encode_eq_iff _ _).mp hs
  · rintro ⟨x, hx, hs⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P T q x hx, hs]

theorem language_invalid (P : Inputs) (T : Test) (s : SignType) (q : List Bool)
    (hq : q ∉ SquareSampleDescriptors.language P) : q ∉ language P T s := fun h => hq h.1

noncomputable def ordinalQuery (P : Inputs) (u : List Bool) : List Bool :=
  pair (pairFst u) (SignStatisticBits.integerCode (SquareSampleHashEnumeration.value P u))

def ordinalFinish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairSnd z)
theorem ordinalFinish_FP : ordinalFinish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem ordinalQuery_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (ordinalQuery P) := by
  have E := (SquareSampleHashEnumeration.evaluator h).withInput.postcompose ordinalFinish ordinalFinish_FP
  exact E.congr (funext fun u => by simp only [ordinalQuery, ordinalFinish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def atOrdinal (P : Inputs) (T : Test) (u : List Bool) : List Bool := value P T (ordinalQuery P u)

theorem ordinal_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) : SpaceFunction (atOrdinal P T) :=
  (ordinalQuery_evaluator h).chain (evaluator h A)

theorem ordinal_packet (P : Inputs) (T : Test) (c : List Bool) (r : Fin (SquareSampleRegularCount.count P c)) :
    atOrdinal P T (pair c (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (sign T c (SquareSampleHashEnumeration.root P c r).val) := by
  have H := value_root P T c (SquareSampleHashEnumeration.root P c r)
  rw [SquareSampleHashEnumeration.hash_root] at H
  simpa only [atOrdinal, ordinalQuery, pairFst_pair] using H

noncomputable def ordinalLanguage (P : Inputs) (T : Test) (s : SignType) : Language :=
  {u | Nat.fromBitsLE (pairSnd u) < SquareSampleRegularCount.count P (pairFst u) ∧
    atOrdinal P T u = InfinitesimalSign.encode s}

def ordinalAccept (s : SignType) (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    pairSnd (pairSnd z) = InfinitesimalSign.encode s)

theorem ordinalAccept_FP (s : SignType) : (fun z => [ordinalAccept s z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  exact ((hi.lt hN).and (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (constFn_mem_FP (InfinitesimalSign.encode s)))).flag_mem_FP

theorem ordinal_decider {P : Inputs} (h : P.Access) {T : Test} (A : T.Access)
    (s : SignType) : SpaceDecider (ordinalLanguage P T s) := by
  have N := (SquareSampleRegularCount.evaluator h).precompose pairFst pairFst_mem_FP
  apply (N.pairOutputs (ordinal_evaluator h A)).withInput.decider (ordinalAccept s) (ordinalAccept_FP s)
  intro u
  simp only [ordinalLanguage, Set.mem_ofPred_eq, ordinalAccept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem ordinal_mem_PSPACE {P : Inputs} (h : P.Access) {T : Test} (A : T.Access)
    (s : SignType) : ordinalLanguage P T s ∈ PSPACE :=
  (ordinal_decider h A s).mem_PSPACE

theorem ordinal_language_packet (P : Inputs) (T : Test) (c : List Bool)
    (r : Fin (SquareSampleRegularCount.count P c)) (s : SignType) :
    pair c (BinaryNatCode.encode r.val) ∈ ordinalLanguage P T s ↔
      sign T c (SquareSampleHashEnumeration.root P c r).val = s := by
  change _ ∧ atOrdinal P T _ = _ ↔ _
  rw [ordinal_packet]
  have hr : Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r.val))) <
      SquareSampleRegularCount.count P (pairFst (pair c (BinaryNatCode.encode r.val))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [and_iff_right hr, encode_eq_iff]

theorem ordinal_language_invalid (P : Inputs) (T : Test) (s : SignType) (u : List Bool)
    (hu : SquareSampleRegularCount.count P (pairFst u) ≤ Nat.fromBitsLE (pairSnd u)) :
    u ∉ ordinalLanguage P T s := fun h => (Nat.not_lt_of_ge hu) h.1

noncomputable def parameterTest (P : Inputs) : Test where
  polynomial := SquareSampleCoordinates.parameter P
  degree := SquareSampleCoordinates.parameterDegree P
  mass := SquareSampleCoordinates.baseHeight P
  polynomial_degree c := (SquareSampleCoordinates.parameter_bounds P c).1
  polynomial_mass c := (SquareSampleCoordinates.parameter_bounds P c).2

noncomputable def parameterAccess {P : Inputs} (h : P.Access) : (parameterTest P).Access :=
  Test.Access.ofPrimitive (SquareSampleCoordinates.parameterDegree_binary h)
    (SquareSampleCoordinates.baseHeight_binary h)
    (SquareSampleCoordinates.parameter_coefficient_evaluator h)

theorem parameter_value (P : Inputs) (c : List Bool) (x : SquareSampleRecordSpan.Root P c) :
    value P (parameterTest P) (pair c (SquareSampleHashChoice.descriptor P c x)) = [] := by
  rw [value_descriptor]
  have hr := ((SquareSampleQueries.mem_roots P c x.val).mp x.property).1
  simp only [sign, parameterTest, Polynomial.eval_map, hr, sign_zero, InfinitesimalSign.encode]

end LeanCanny.Encoding.SquareSampleTestSign
