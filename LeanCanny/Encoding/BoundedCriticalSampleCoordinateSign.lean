/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleIndexedSign
public import LeanCanny.Encoding.BoundedCriticalSampleCoordinateTests

/-! # Native coordinate signs of actual critical samples

Queries have the form `pair (pair source descriptor) coordinateIndex`.
The coordinate index is normalized without changing the sample descriptor.
Numerator and denominator readers are constructed from the source readers.
Validated languages reject invalid descriptors and out-of-range coordinates.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleCoordinateSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Brackets
open BoundedCriticalSampleCoordinateTests
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleIndexedSign.value
  BoundedCriticalSampleIndexedSign.probeContext BoundedCriticalSampleIndexedSign.baseContext
  numerator denominator

def origin (q : List Bool) : List Bool := pairFst (pairFst q)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def normalizeQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.normalize (pairSnd q))
theorem normalizeQuery_FP : normalizeQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def value (P : Readers) (q : List Bool) : List Bool :=
  BoundedCriticalSampleTestSign.multiplyTags (pair
    (BoundedCriticalSampleIndexedSign.value P (numerator P) (normalizeQuery q))
    (BoundedCriticalSampleIndexedSign.value P (denominator P) (normalizeQuery q)))

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) :=
  (((BoundedCriticalSampleIndexedSign.evaluator h (numeratorAccess h ha) ha).precompose
    normalizeQuery normalizeQuery_FP).pairOutputs
      ((BoundedCriticalSampleIndexedSign.evaluator h (denominatorAccess h ha) ha).precompose
        normalizeQuery normalizeQuery_FP)).postcompose
    BoundedCriticalSampleTestSign.multiplyTags BoundedCriticalSampleTestSign.multiplyTags_FP

theorem value_sample (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (i : Fin (P.dim c + 4)) :
    value P (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) (BinaryNatCode.encode i.val)) =
      InfinitesimalSign.encode (SignType.sign (x.val i)) := by
  simp only [value, normalizeQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, BinaryNat.normalize_bits]
  rw [BoundedCriticalSampleIndexedSign.value_sample, BoundedCriticalSampleIndexedSign.value_sample,
    BoundedCriticalSampleTestSign.multiplyTags_packet]
  exact congrArg InfinitesimalSign.encode (coordinate_sign P c x i)

theorem value_at (P : Readers) (q : List Bool) (x : BoundedFullCriticalSamples.Samples P (origin q))
    (hx : BoundedCriticalSampleHashChoice.descriptor P (origin q) x = pairSnd (pairFst q))
    (hi : Nat.fromBitsLE (pairSnd q) < P.dim (origin q) + 4) :
    value P q = InfinitesimalSign.encode (SignType.sign (x.val ⟨Nat.fromBitsLE (pairSnd q), hi⟩)) := by
  have hq : value P q = value P (pair (pair (origin q) (pairSnd (pairFst q)))
      (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q)))) := by
    simp only [value, normalizeQuery, origin, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
      BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits, BoundedCriticalSampleIndexedSign.value,
      BoundedCriticalSampleIndexedSign.probeContext, BoundedCriticalSampleIndexedSign.baseContext,
      BoundedCriticalSampleTestSign.probeContext, BoundedCriticalSampleIndexedSign.origin]
  rw [hq, ← hx, value_sample P (origin q) x ⟨Nat.fromBitsLE (pairSnd q), hi⟩]

theorem value_index_word (P : Readers) (c w d : List Bool) :
    value P (pair (pair c w) d) = value P (pair (pair c w) (BinaryNatCode.encode (Nat.fromBitsLE d))) := by
  simp only [value, normalizeQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]

noncomputable def language (P : Readers) (s : SignType) : Language :=
  {q | pairFst q ∈ BoundedCriticalSampleDescriptors.language P ∧
    Nat.fromBitsLE (pairSnd q) < P.dim (origin q) + 4 ∧ value P q = InfinitesimalSign.encode s}

def accept (P : Readers) (s : SignType) (z : List Bool) : Bool := decide
  (pairFst (pairSnd z) = [true] ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < P.dim (origin (pairFst z)) + 4 ∧
    pairSnd (pairSnd z) = InfinitesimalSign.encode s)

theorem accept_FP {P : Readers} (h : P.PolyTime) (s : SignType) : (fun z => [accept P s z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have ho : (fun z => origin (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := origin) pairFst_mem_FP origin_FP
  have hn : BinaryFn (fun z => P.dim (origin (pairFst z)) + 4) :=
    (BinaryFn.ofUnary (h.dim.comp ho)).add (BinaryFn.const 4)
  exact ((stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (constFn_mem_FP [true])).and
    ((hi.lt hn).and (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
      (constFn_mem_FP (InfinitesimalSign.encode s))))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (language P s) := by
  have V := ((BoundedCriticalSampleDescriptors.decider h ha).precompose pairFst pairFst_mem_FP).flagEvaluator
  apply (V.pairOutputs (evaluator h ha)).withInput.decider (accept P s) (accept_FP h s)
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, accept, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : language P s ∈ PSPACE :=
  (decider h ha s).mem_PSPACE

theorem language_iff (P : Readers) (s : SignType) (q : List Bool) : q ∈ language P s ↔
    ∃ (x : BoundedFullCriticalSamples.Samples P (origin q))
      (hi : Nat.fromBitsLE (pairSnd q) < P.dim (origin q) + 4),
      BoundedCriticalSampleHashChoice.descriptor P (origin q) x = pairSnd (pairFst q) ∧
        SignType.sign (x.val ⟨Nat.fromBitsLE (pairSnd q), hi⟩) = s := by
  constructor
  · rintro ⟨⟨x, hx⟩, hi, hs⟩
    refine ⟨x, hi, hx, ?_⟩
    rw [value_at P q x hx hi] at hs
    exact (BoundedCriticalSampleTestSign.encode_eq_iff _ _).mp hs
  · rintro ⟨x, hi, hx, hs⟩
    refine ⟨⟨x, hx⟩, hi, ?_⟩
    rw [value_at P q x hx hi, hs]

theorem language_invalid_descriptor (P : Readers) (s : SignType) (q : List Bool)
    (hq : pairFst q ∉ BoundedCriticalSampleDescriptors.language P) : q ∉ language P s := fun h => hq h.1

theorem language_invalid_coordinate (P : Readers) (s : SignType) (q : List Bool)
    (hq : P.dim (origin q) + 4 ≤ Nat.fromBitsLE (pairSnd q)) : q ∉ language P s :=
  fun h => (Nat.not_lt_of_ge hq) h.2.1

noncomputable def atOrdinal (P : Readers) (q : List Bool) : List Bool :=
  value P (BoundedCriticalSampleIndexedSign.ordinalQuery P q)

theorem ordinal_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (atOrdinal P) :=
  (BoundedCriticalSampleIndexedSign.ordinalQuery_evaluator h ha).chain (evaluator h ha)

theorem ordinal_packet (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c))
    (i : Fin (P.dim c + 4)) :
    atOrdinal P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode i.val)) =
      InfinitesimalSign.encode (SignType.sign ((BoundedCriticalSampleHashEnumeration.sampleEquiv P c r).val i)) := by
  rw [atOrdinal, BoundedCriticalSampleIndexedSign.ordinalQuery_packet, value_sample]

noncomputable def ordinalLanguage (P : Readers) (s : SignType) : Language :=
  {q | Nat.fromBitsLE (pairSnd (pairFst q)) < BoundedCriticalSampleCount.count P (origin q) ∧
    Nat.fromBitsLE (pairSnd q) < P.dim (origin q) + 4 ∧ atOrdinal P q = InfinitesimalSign.encode s}

def ordinalAccept (P : Readers) (s : SignType) (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < P.dim (origin (pairFst z)) + 4 ∧
    pairSnd (pairSnd z) = InfinitesimalSign.encode s)

theorem ordinalAccept_FP {P : Readers} (h : P.PolyTime) (s : SignType) :
    (fun z => [ordinalAccept P s z]) ∈ FP := by
  have hr := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have ho : (fun z => origin (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := origin) pairFst_mem_FP origin_FP
  have hn : BinaryFn (fun z => P.dim (origin (pairFst z)) + 4) :=
    (BinaryFn.ofUnary (h.dim.comp ho)).add (BinaryFn.const 4)
  exact ((hr.lt hN).and ((hi.lt hn).and
    (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
      (constFn_mem_FP (InfinitesimalSign.encode s))))).flag_mem_FP

theorem ordinal_decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (ordinalLanguage P s) := by
  have N := (BoundedCriticalSampleCount.evaluator h ha).precompose origin origin_FP
  apply (N.pairOutputs (ordinal_evaluator h ha)).withInput.decider (ordinalAccept P s) (ordinalAccept_FP h s)
  intro q
  simp only [ordinalLanguage, Set.mem_ofPred_eq, ordinalAccept, Function.comp_apply, pairFst_pair,
    pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem ordinal_mem_PSPACE {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : ordinalLanguage P s ∈ PSPACE :=
  (ordinal_decider h ha s).mem_PSPACE

theorem ordinal_language_packet (P : Readers) (c : List Bool) (r : Fin (BoundedCriticalSampleCount.count P c))
    (i : Fin (P.dim c + 4)) (s : SignType) :
    pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode i.val) ∈ ordinalLanguage P s ↔
      SignType.sign ((BoundedCriticalSampleHashEnumeration.sampleEquiv P c r).val i) = s := by
  change _ ∧ _ ∧ atOrdinal P _ = _ ↔ _
  rw [ordinal_packet]
  simp only [origin, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    r.isLt, i.isLt, true_and, BoundedCriticalSampleTestSign.encode_eq_iff]

theorem ordinal_language_invalid (P : Readers) (s : SignType) (q : List Bool)
    (hq : BoundedCriticalSampleCount.count P (origin q) ≤ Nat.fromBitsLE (pairSnd (pairFst q))) :
    q ∉ ordinalLanguage P s := fun h => (Nat.not_lt_of_ge hq) h.1

theorem ordinal_language_invalid_coordinate (P : Readers) (s : SignType) (q : List Bool)
    (hq : P.dim (origin q) + 4 ≤ Nat.fromBitsLE (pairSnd q)) : q ∉ ordinalLanguage P s :=
  fun h => (Nat.not_lt_of_ge hq) h.2.1

end LeanCanny.Encoding.BoundedCriticalSampleCoordinateSign
