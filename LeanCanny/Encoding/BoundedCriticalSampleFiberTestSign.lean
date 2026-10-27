/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberTestProbeSource
public import LeanCanny.Encoding.BoundedCriticalSampleFiberOrderedRoot
public import LeanCanny.Algebra.RationalCutSpace

/-! # Native arbitrary polynomial signs at ordered fiber roots

The queried root is given by its short real-order ordinal. Hash selection,
rank conversion, weighted moments, and both determinant signs are computed
internally. Only the test polynomial's original modular readers are leaves.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberTestSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleFiberTestMoments
open scoped Classical

def query (u : List Bool) : List Bool := pair u (BinaryNatCode.encode 0)
theorem query_FP : query ∈ FP := mem_FP_pair id_mem_FP (constFn_mem_FP _)
noncomputable def descriptor (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : List Bool :=
  BoundedCriticalSampleFiberSignatureRead.descriptor P F (BoundedCriticalSampleFiberOrderedRoot.signQuery P F (query u))
theorem descriptor_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (descriptor P F) :=
  ((BoundedCriticalSampleFiberOrderedRoot.signQuery_evaluator h A ha).precompose query query_FP).chain
    (BoundedCriticalSampleFiberSignatureRead.descriptor_evaluator h A ha)

theorem descriptor_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    descriptor P F (pair c (BinaryNatCode.encode r.val)) = BoundedCriticalSampleFiberProbeSource.context P F c
      (BoundedCriticalSampleFiberHashChoice.hash P F c (BoundedCriticalSampleFiberOrderedRoot.root P F c r)) 0 := by
  simp only [descriptor, query, BoundedCriticalSampleFiberOrderedRoot.signQuery, pairFst_pair, pairSnd_pair]
  rw [BoundedCriticalSampleFiberSignatureRead.descriptor_packet]
  rw [BoundedCriticalSampleFiberOrderedRoot.root, BoundedCriticalSampleFiberHashEnumeration.hash_root]

noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (u : List Bool) : List Bool :=
  InfinitesimalSign.encode (SignType.sign (BoundedCriticalSampleFiberTestProbe.firstCoefficient P F G (descriptor P F u)) *
    SignType.sign (BoundedCriticalSampleFiberProbeCoefficient.firstCoefficient P F true (descriptor P F u)))

attribute [local irreducible] BoundedCriticalSampleFiberTestProbe.firstCoefficient BoundedCriticalSampleFiberProbeCoefficient.firstCoefficient descriptor

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access) {G : BoundedAlgebraicSlice.Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F G) := by
  have D := descriptor_evaluator h A ha
  have L := D.chain (BoundedCriticalSampleFiberTestProbe.sign_evaluator h A B ha)
  have R := D.chain (BoundedCriticalSampleFiberProbeCoefficient.sign_evaluator h A ha true)
  have E := (L.pairOutputs R).postcompose BoundedCriticalSampleFiberSignatureRead.multiplyTags BoundedCriticalSampleFiberSignatureRead.multiplyTags_FP
  exact E.congr (funext fun u => by
    simp only [Function.comp_apply, BoundedCriticalSampleFiberSignatureRead.multiplyTags_packet, value])

theorem value_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    value P F G (pair c (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (sign P G c (BoundedCriticalSampleFiberOrderedRoot.root P F c r).val) := by
  rw [value, descriptor_packet, BoundedCriticalSampleFiberTestProbeSource.pointwise]

theorem value_original (P : Readers) (F G : BoundedAlgebraicSlice.Family) (c : List Bool)
    (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    value P F G (pair c (BinaryNatCode.encode r.val)) =
      InfinitesimalSign.encode (SignType.sign ((BoundedCriticalSampleSlice.specialized P G c).eval
        (BoundedCriticalSampleFiberRoot.root P F c r).val)) := by
  rw [value_packet, BoundedCriticalSampleFiberOrderedRoot.root_eq_original]
  rfl

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (s : SignType) : Language :=
  {u | Nat.fromBitsLE (pairSnd u) < BoundedCriticalSampleSlice.RootCount.count P F (pairFst u) ∧
    value P F G u = InfinitesimalSign.encode s}

def accept (s : SignType) (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    pairSnd (pairSnd z) = InfinitesimalSign.encode s)
theorem accept_FP (s : SignType) : (fun z => [accept s z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  exact ((hi.lt hN).and (Brackets.stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (constFn_mem_FP (InfinitesimalSign.encode s)))).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access) {G : BoundedAlgebraicSlice.Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (language P F G s) := by
  have N := (BoundedCriticalSampleSlice.RootCount.count_evaluator h A ha).precompose pairFst pairFst_mem_FP
  apply (N.pairOutputs (evaluator h A B ha)).withInput.decider (accept s) (accept_FP s)
  intro u
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem language_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) (s : SignType) :
    pair c (BinaryNatCode.encode r.val) ∈ language P F G s ↔ sign P G c (BoundedCriticalSampleFiberOrderedRoot.root P F c r).val = s := by
  change _ ∧ value P F G _ = _ ↔ _
  rw [value_packet]
  have hr : Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode r.val))) <
      BoundedCriticalSampleSlice.RootCount.count P F (pairFst (pair c (BinaryNatCode.encode r.val))) := by
    simpa only [pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [and_iff_right hr]
  generalize sign P G c (BoundedCriticalSampleFiberOrderedRoot.root P F c r).val = a
  cases a <;> cases s <;> decide

theorem language_invalid (P : Readers) (F : BoundedAlgebraicSlice.Family) (G : BoundedAlgebraicSlice.Family) (s : SignType) (u : List Bool)
    (hu : BoundedCriticalSampleSlice.RootCount.count P F (pairFst u) ≤ Nat.fromBitsLE (pairSnd u)) : u ∉ language P F G s := by
  intro h
  exact (Nat.not_lt_of_ge hu) h.1

theorem language_mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : BoundedAlgebraicSlice.Family}
    (A : F.Access) (B : G.Access) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    language P F G s ∈ PSPACE := (decider h A B ha s).mem_PSPACE

end LeanCanny.Encoding.BoundedCriticalSampleFiberTestSign
