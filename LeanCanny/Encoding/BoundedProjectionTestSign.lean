/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionTestProbeSource
public import LeanCanny.Encoding.BoundedProjectionOrderedRoot
public import LeanCanny.Algebra.RationalCutSpace

/-! # Native arbitrary polynomial signs at ordered projection roots

The queried root is given by its short real-order ordinal. Hash selection,
rank conversion, weighted moments, and both determinant signs are computed
internally. Only the test polynomial's original modular readers are leaves.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionTestSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionTestMoments
open scoped Classical

def query (u : List Bool) : List Bool := pair u (BinaryNatCode.encode 0)
theorem query_FP : query ∈ FP := mem_FP_pair id_mem_FP (constFn_mem_FP _)
noncomputable def descriptor (P : Readers) (u : List Bool) : List Bool :=
  BoundedProjectionSignatureRead.descriptor P (BoundedProjectionOrderedRoot.signQuery P (query u))
theorem descriptor_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (descriptor P) :=
  ((BoundedProjectionOrderedRoot.signQuery_evaluator h ha).precompose query query_FP).chain
    (BoundedProjectionSignatureRead.descriptor_evaluator h ha)

theorem descriptor_packet (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    descriptor P (pair c (BinaryNatCode.encode r.val)) = BoundedProjectionProbeSource.context P c
      (BoundedProjectionHashChoice.hash P c (BoundedProjectionOrderedRoot.root P c r)) 0 := by
  simp only [descriptor, query, BoundedProjectionOrderedRoot.signQuery, pairFst_pair, pairSnd_pair]
  rw [BoundedProjectionSignatureRead.descriptor_packet]
  rw [BoundedProjectionOrderedRoot.root, BoundedProjectionHashEnumeration.hash_root]

noncomputable def value (P : Readers) (T : Test) (u : List Bool) : List Bool :=
  InfinitesimalSign.encode (SignType.sign (BoundedProjectionTestProbe.firstCoefficient P T (descriptor P u)) *
    SignType.sign (BoundedProjectionProbeCoefficient.firstCoefficient P true (descriptor P u)))

attribute [local irreducible] BoundedProjectionTestProbe.firstCoefficient BoundedProjectionProbeCoefficient.firstCoefficient descriptor

theorem evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P T) := by
  have D := descriptor_evaluator h ha
  have L := D.chain (BoundedProjectionTestProbe.sign_evaluator h A ha)
  have R := D.chain (BoundedProjectionProbeCoefficient.sign_evaluator h ha true)
  have E := (L.pairOutputs R).postcompose BoundedProjectionSignatureRead.multiplyTags BoundedProjectionSignatureRead.multiplyTags_FP
  exact E.congr (funext fun u => by
    simp only [Function.comp_apply, BoundedProjectionSignatureRead.multiplyTags_packet, value])

theorem value_packet (P : Readers) (T : Test) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    value P T (pair c (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (sign T c (BoundedProjectionOrderedRoot.root P c r).val) := by
  rw [value, descriptor_packet, BoundedProjectionTestProbeSource.pointwise]

noncomputable def language (P : Readers) (T : Test) (s : SignType) : Language :=
  {u | Nat.fromBitsLE (pairSnd u) < BoundedProjectionRootCount.count P (pairFst u) ∧
    value P T u = InfinitesimalSign.encode s}

def accept (s : SignType) (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    pairSnd (pairSnd z) = InfinitesimalSign.encode s)
theorem accept_FP (s : SignType) : (fun z => [accept s z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  exact ((hi.lt hN).and (Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (constFn_mem_FP (InfinitesimalSign.encode s)))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (language P T s) := by
  have N := (BoundedProjectionRootCount.evaluator h ha).precompose pairFst pairFst_mem_FP
  apply (N.pairOutputs (evaluator h A ha)).withInput.decider (accept s) (accept_FP s)
  intro u
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem language_packet (P : Readers) (T : Test) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (s : SignType) :
    pair c (BinaryNatCode.encode r.val) ∈ language P T s ↔ sign T c (BoundedProjectionOrderedRoot.root P c r).val = s := by
  change _ ∧ value P T _ = _ ↔ _
  rw [value_packet]
  have hr : Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r.val))) <
      BoundedProjectionRootCount.count P (pairFst (pair c (BinaryNatCode.encode r.val))) := by
    simpa only [pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [and_iff_right hr]
  generalize sign T c (BoundedProjectionOrderedRoot.root P c r).val = a
  cases a <;> cases s <;> decide

theorem language_invalid (P : Readers) (T : Test) (s : SignType) (u : List Bool)
    (hu : BoundedProjectionRootCount.count P (pairFst u) ≤ Nat.fromBitsLE (pairSnd u)) : u ∉ language P T s := by
  intro h
  exact (Nat.not_lt_of_ge hu) h.1

noncomputable def rationalCut : Test where
  polynomial := RationalCutBits.polynomial
  degree _ := 1
  mass := RationalCutBits.massExponent
  polynomial_degree := RationalCutBits.polynomial_degree
  polynomial_mass := RationalCutBits.polynomial_mass

noncomputable def rationalCutAccess : rationalCut.Access where
  degree_binary := BinaryFn.const 1
  mass_binary := BinaryFn.ofUnary RationalCutBits.massExponent_unary
  coefficient := RationalCutBits.coefficient
  coefficient_eq := RationalCutBits.coefficient_packet
  evaluator := SpaceFunction.ofFP _ RationalCutBits.coefficient_FP

theorem rationalCut_below (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    pair c (BinaryNatCode.encode r.val) ∈ language P rationalCut .neg ↔
      (BoundedProjectionOrderedRoot.root P c r).val < RationalCutBits.threshold c := by
  rw [language_packet]
  exact RationalCutBits.sign_neg_iff c _

end LeanCanny.Encoding.BoundedProjectionTestSign
