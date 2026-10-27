/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTermTest
public import LeanCanny.ETR.FormulaBooleanCircuitBridge

/-! # Native formula truth and marking at actual critical samples

Each atom uses the native cleared-term sign reader at the original sample
descriptor. The Boolean circuit comes from the original formula syntax.
Only its polynomial-size Boolean table is stored. Guarded descriptor and
ordinal languages refer to the actual sample tuple, extended by zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFormula
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Brackets
open scoped Classical
attribute [local irreducible] BoundedCriticalSampleIndexedSign.value BoundedCriticalSampleTermTest.test
  FormulaBooleanCircuitSource.circuit FormulaBooleanCircuitSource.requested

def termReader (read : List Bool → List Bool) : List Bool → List Bool :=
  FormulaBooleanCircuitSource.termCode ∘ FormulaBooleanCircuitSource.readerQuery read
theorem termReader_FP (read : List Bool → List Bool) (hr : read ∈ FP) : termReader read ∈ FP :=
  FormulaBooleanCircuitSource.termCodeOfReader_FP read hr

def requestQuery (read : List Bool → List Bool) (q : List Bool) : List Bool :=
  FormulaBooleanCircuitSource.readerQuery read (pair (BoundedCriticalSampleIndexedSign.origin q) (pairSnd q))
theorem requestQuery_FP (read : List Bool → List Bool) (hr : read ∈ FP) : requestQuery read ∈ FP :=
  mem_FP_comp (mem_FP_pair BoundedCriticalSampleIndexedSign.origin_FP pairSnd_mem_FP)
    (FormulaBooleanCircuitSource.readerQuery_FP read hr)

noncomputable def atom (P : Readers) (read : List Bool → List Bool) (q : List Bool) : Bool := decide
  (BoundedCriticalSampleIndexedSign.value P (BoundedCriticalSampleTermTest.test P (termReader read)) q =
    InfinitesimalSign.encode (FormulaBooleanCircuitSource.requested (requestQuery read q)))

def atomFinish (read : List Bool → List Bool) (z : List Bool) : List Bool :=
  [decide (pairSnd z = InfinitesimalSign.encode (FormulaBooleanCircuitSource.requested (requestQuery read (pairFst z))))]
theorem atomFinish_FP (read : List Bool → List Bool) (hr : read ∈ FP) : atomFinish read ∈ FP :=
  (stringEq_fppred pairSnd_mem_FP (mem_FP_comp (mem_FP_comp pairFst_mem_FP (requestQuery_FP read hr))
    FormulaBooleanCircuitSource.requested_FP)).flag_mem_FP

theorem atom_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (fun q => [atom P read q]) := by
  have E := BoundedCriticalSampleIndexedSign.evaluator h
    (BoundedCriticalSampleTermTest.access h (termReader read) (termReader_FP read hr) ha) ha
  exact (E.withInput.postcompose (atomFinish read) (atomFinish_FP read hr)).congr
    (funext fun q => by simp only [atomFinish, atom, Function.comp_apply, pairFst_pair, pairSnd_pair])

def pointQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd q)
theorem pointQuery_FP : pointQuery ∈ FP := mem_FP_pair pairFst_mem_FP pairSnd_mem_FP

noncomputable def value (P : Readers) (read : List Bool → List Bool) (q : List Bool) : Bool :=
  BooleanCircuitSpace.value (FormulaBooleanCircuitSource.circuit.comp (read ∘ pairFst)) (atom P read) (pointQuery q)

theorem evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (fun q => [value P read q]) :=
  (BooleanCircuitSpace.evaluator _ (FormulaBooleanCircuitSource.circuit_access.comp (read ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP hr)) _ (atom_evaluator h read hr ha)).precompose pointQuery pointQuery_FP

theorem atom_sample (P : Readers) (read : List Bool → List Bool) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) (k : ℕ) :
    atom P read (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) (BinaryNatCode.encode k)) =
      FormulaBooleanCircuitSource.atom (fun t => SignType.sign (t.eval (Formula.extend x.val)))
        (pair (read c) (BinaryNatCode.encode k)) := by
  rw [atom, BoundedCriticalSampleTermTest.value_sample]
  simp only [termReader, Function.comp_apply, requestQuery, BoundedCriticalSampleIndexedSign.origin,
    FormulaBooleanCircuitSource.readerQuery, pairFst_pair, pairSnd_pair, FormulaBooleanCircuitSource.atom,
    FormulaBooleanCircuitSource.term, BoundedCriticalSampleTestSign.encode_eq_iff]
  rfl

theorem value_sample (P : Readers) (read : List Bool → List Bool) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) :
    value P read (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) =
      FormulaBooleanCircuitSource.evalSign (fun t => SignType.sign (t.eval (Formula.extend x.val)))
        (FormulaView.formula (read c)) := by
  simp only [value, pointQuery, pairFst_pair, pairSnd_pair]
  rw [BooleanCircuitSpace.value_comp _ _ _
    (FormulaBooleanCircuitSource.atom (fun t => SignType.sign (t.eval (Formula.extend x.val)))) _
      (fun k _ => by simpa only [Function.comp_apply, pairFst_pair] using atom_sample P read c x k)]
  simpa only [Function.comp_apply, pairFst_pair] using
    FormulaBooleanCircuitSource.value_formula (fun t => SignType.sign (t.eval (Formula.extend x.val))) (read c)

theorem value_at (P : Readers) (read : List Bool → List Bool) (q : List Bool)
    (x : BoundedFullCriticalSamples.Samples P (pairFst q))
    (hx : BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q) :
    value P read q = FormulaBooleanCircuitSource.evalSign (fun t => SignType.sign (t.eval (Formula.extend x.val)))
      (FormulaView.formula (read (pairFst q))) := by
  simpa only [value, pointQuery, pairFst_pair, pairSnd_pair, hx] using value_sample P read (pairFst q) x

noncomputable def language (P : Readers) (read : List Bool → List Bool) : Language :=
  {q | q ∈ BoundedCriticalSampleDescriptors.language P ∧ value P read q = true}

def accept (z : List Bool) : Bool := decide (pairFst z = [true] ∧ pairSnd z = [true])
theorem accept_FP : (fun z => [accept z]) ∈ FP :=
  ((stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).and
    (stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P read) := by
  have V := (BoundedCriticalSampleDescriptors.decider h ha).flagEvaluator
  apply (V.pairOutputs (evaluator h read hr ha)).decider accept accept_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, accept, pairFst_pair, pairSnd_pair,
    List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : language P read ∈ PSPACE :=
  (decider h read hr ha).mem_PSPACE

theorem language_iff (P : Readers) (read : List Bool → List Bool) (q : List Bool) : q ∈ language P read ↔
    ∃ x : BoundedFullCriticalSamples.Samples P (pairFst q),
      BoundedCriticalSampleHashChoice.descriptor P (pairFst q) x = pairSnd q ∧
        (FormulaView.formula (read (pairFst q))).Holds (Formula.extend x.val) := by
  constructor
  · rintro ⟨⟨x, hx⟩, hv⟩
    refine ⟨x, hx, ?_⟩
    rw [value_at P read q x hx, FormulaBooleanCircuitSource.evalSign_holds] at hv
    exact hv
  · rintro ⟨x, hx, hv⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [value_at P read q x hx, FormulaBooleanCircuitSource.evalSign_holds]
    exact hv

theorem language_invalid (P : Readers) (read : List Bool → List Bool) (q : List Bool)
    (hq : q ∉ BoundedCriticalSampleDescriptors.language P) : q ∉ language P read := fun h => hq h.1

theorem language_sample (P : Readers) (read : List Bool → List Bool) (c : List Bool)
    (x : BoundedFullCriticalSamples.Samples P c) :
    pair c (BoundedCriticalSampleHashChoice.descriptor P c x) ∈ language P read ↔
      (FormulaView.formula (read c)).Holds (Formula.extend x.val) := by
  change _ ∧ value P read _ = true ↔ _
  rw [value_sample, FormulaBooleanCircuitSource.evalSign_holds]
  apply and_iff_right
  change ∃ y : BoundedFullCriticalSamples.Samples P
    (pairFst (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))),
      BoundedCriticalSampleHashChoice.descriptor P _ y = pairSnd (pair c (BoundedCriticalSampleHashChoice.descriptor P c x))
  rw [pairFst_pair, pairSnd_pair]
  exact ⟨x, rfl⟩

theorem marking_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => [decide (q ∈ language P read)]) := (decider h read hr ha).flagEvaluator

noncomputable def atOrdinal (P : Readers) (read : List Bool → List Bool) (q : List Bool) : Bool :=
  value P read (BoundedCriticalSampleTestSign.ordinalQuery P q)

theorem ordinal_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (fun q => [atOrdinal P read q]) :=
  (BoundedCriticalSampleTestSign.ordinalQuery_evaluator h ha).chain (evaluator h read hr ha)

theorem ordinal_packet (P : Readers) (read : List Bool → List Bool) (c : List Bool)
    (r : Fin (BoundedCriticalSampleCount.count P c)) :
    atOrdinal P read (pair c (BinaryNatCode.encode r.val)) =
      FormulaBooleanCircuitSource.evalSign
        (fun t => SignType.sign (t.eval (Formula.extend (BoundedCriticalSampleHashEnumeration.sampleEquiv P c r).val)))
        (FormulaView.formula (read c)) := by
  have hq : BoundedCriticalSampleTestSign.ordinalQuery P (pair c (BinaryNatCode.encode r.val)) =
      pair c (BoundedCriticalSampleHashChoice.descriptor P c (BoundedCriticalSampleHashEnumeration.sampleEquiv P c r)) := by
    simp only [BoundedCriticalSampleTestSign.ordinalQuery, pairFst_pair,
      BoundedCriticalSampleHashEnumeration.descriptor_sample]
  rw [atOrdinal, hq, value_sample]

noncomputable def ordinalLanguage (P : Readers) (read : List Bool → List Bool) : Language :=
  {q | Nat.fromBitsLE (pairSnd q) < BoundedCriticalSampleCount.count P (pairFst q) ∧ atOrdinal P read q = true}

def ordinalAccept (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧ pairSnd (pairSnd z) = [true])
theorem ordinalAccept_FP : (fun z => [ordinalAccept z]) ∈ FP :=
  (((BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)).lt
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))).and
      (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [true]))).flag_mem_FP

theorem ordinal_decider {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (ordinalLanguage P read) := by
  have N := (BoundedCriticalSampleCount.evaluator h ha).precompose pairFst pairFst_mem_FP
  apply (N.pairOutputs (ordinal_evaluator h read hr ha)).withInput.decider ordinalAccept ordinalAccept_FP
  intro q
  simp only [ordinalLanguage, Set.mem_ofPred_eq, ordinalAccept, Function.comp_apply, pairFst_pair,
    pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, List.cons.injEq, and_true, decide_eq_true_eq]

theorem ordinal_mem_PSPACE {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : ordinalLanguage P read ∈ PSPACE :=
  (ordinal_decider h read hr ha).mem_PSPACE

theorem ordinal_language_packet (P : Readers) (read : List Bool → List Bool) (c : List Bool)
    (r : Fin (BoundedCriticalSampleCount.count P c)) :
    pair c (BinaryNatCode.encode r.val) ∈ ordinalLanguage P read ↔
      (FormulaView.formula (read c)).Holds (Formula.extend (BoundedCriticalSampleHashEnumeration.sampleEquiv P c r).val) := by
  change _ ∧ atOrdinal P read _ = true ↔ _
  rw [ordinal_packet, FormulaBooleanCircuitSource.evalSign_holds]
  have hr : Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r.val))) <
      BoundedCriticalSampleCount.count P (pairFst (pair c (BinaryNatCode.encode r.val))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  exact and_iff_right hr

theorem ordinal_language_invalid (P : Readers) (read : List Bool → List Bool) (q : List Bool)
    (hq : BoundedCriticalSampleCount.count P (pairFst q) ≤ Nat.fromBitsLE (pairSnd q)) :
    q ∉ ordinalLanguage P read := fun h => (Nat.not_lt_of_ge hq) h.1

theorem ordinal_marking_evaluator {P : Readers} (h : P.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => [decide (q ∈ ordinalLanguage P read)]) := (ordinal_decider h read hr ha).flagEvaluator

end LeanCanny.Encoding.BoundedCriticalSampleFormula
