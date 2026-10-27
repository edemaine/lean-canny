/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRootRank
public import LeanCanny.Computation.BoundedChoice

/-! # Native conversion from real-order root indices to symbolic labels

Bounded search inverts the native real-order rank. The selected hash ordinal
denotes exactly the original fiber root at the requested real-order index.
Repeated roots count once. All selection work is charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberOrderedRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

def source (s : List Bool) : List Bool := pairFst (pairFst s)
def rankQuery (s : List Bool) : List Bool := pair (source s) (pairSnd s)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem rankQuery_FP : rankQuery ∈ FP := mem_FP_pair source_FP pairSnd_mem_FP

noncomputable def language (P : Readers) (F : BoundedAlgebraicSlice.Family) : Language := {s |
  Nat.fromBitsLE (pairSnd s) < BoundedCriticalSampleSlice.RootCount.count P F (source s) ∧
    BoundedCriticalSampleFiberRootRank.value P F (rankQuery s) = Nat.fromBitsLE (pairSnd (pairFst s))}

def accept (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    Nat.fromBitsLE (pairSnd (pairSnd z)) = Nat.fromBitsLE (pairSnd (pairFst (pairFst z))))
theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hc := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  have hj := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact ((hj.lt hN).and (hr.eq hc)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) := by
  have N := (BoundedCriticalSampleSlice.RootCount.count_evaluator h A ha).precompose source source_FP
  have R := (BoundedCriticalSampleFiberRootRank.evaluator h A ha).precompose rankQuery rankQuery_FP
  apply (N.pairOutputs R).withInput.decider accept accept_FP
  intro s
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

noncomputable def bound (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := F.degree (BoundedCriticalSampleSlice.context (pairFst u))
theorem bound_binary {F : BoundedAlgebraicSlice.Family} (A : F.Access) : BinaryFn (bound F) :=
  A.degree_binary.comp (mem_FP_comp pairFst_mem_FP BoundedCriticalSampleSlice.context_FP)

noncomputable def index (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := BoundedChoice.search (language P F) u (bound F u) - 1
theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (index P F u)) := by
  have E := BoundedChoice.evaluator (decider h A ha) (fun u => BinaryNatCode.encode (bound F u)) (bound_binary A).bits_mem_FP
  exact E.congr (funext fun u => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, index])

attribute [local irreducible] language index

theorem index_spec (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    index P F (pair c (BinaryNatCode.encode r.val)) < BoundedCriticalSampleSlice.RootCount.count P F c ∧
      BoundedCriticalSampleFiberRootRank.value P F (pair c (BinaryNatCode.encode (index P F (pair c (BinaryNatCode.encode r.val))))) = r.val := by
  obtain ⟨a, ha⟩ := BoundedCriticalSampleFiberRootRank.exists_rank P F c r.val r.isLt
  have hN : BoundedCriticalSampleSlice.RootCount.count P F c ≤ F.degree (BoundedCriticalSampleSlice.context c) :=
    BoundedCriticalSampleFiberRoot.count_le_degree P F c
  have hex : ∃ j < bound F (pair c (BinaryNatCode.encode r.val)),
      pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode j) ∈ language P F := by
    refine ⟨a.val, ?_, ?_⟩
    · simpa only [bound, pairFst_pair] using a.isLt.trans_le hN
    · simp only [language, Set.mem_ofPred_eq, source, rankQuery, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact ⟨a.isLt, (BoundedCriticalSampleFiberRootRank.value_packet P F c a).trans ha⟩
  have hw := (BoundedChoice.witness (language P F) _ _ hex).2
  unfold index
  simpa only [language, Set.mem_ofPred_eq, source, rankQuery, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] using hw

noncomputable def root (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    BoundedCriticalSampleFiberRecordSpan.Root P F c :=
  BoundedCriticalSampleFiberHashEnumeration.root P F c ⟨index P F (pair c (BinaryNatCode.encode r.val)), (index_spec P F c r).1⟩

theorem root_eq_ordered (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    root P F c r = (BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin (k := BoundedCriticalSampleSlice.RootCount.count P F c) rfl r := by
  apply ((BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin (k := BoundedCriticalSampleSlice.RootCount.count P F c) rfl).symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  change BoundedCriticalSampleFiberRootOrder.rank P F c
    ⟨index P F (pair c (BinaryNatCode.encode r.val)), (index_spec P F c r).1⟩ = r.val
  rw [← BoundedCriticalSampleFiberRootRank.value_packet]
  exact (index_spec P F c r).2

theorem root_strictMono (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : StrictMono (fun r => (root P F c r).val) := by
  intro a b hab
  change (root P F c a).val < (root P F c b).val
  rw [root_eq_ordered P F c a, root_eq_ordered P F c b]
  exact ((BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin (k := BoundedCriticalSampleSlice.RootCount.count P F c) rfl).strictMono hab

theorem root_surjective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Surjective (root P F c) := by
  intro x
  refine ⟨((BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin (k := BoundedCriticalSampleSlice.RootCount.count P F c) rfl).symm x, ?_⟩
  rw [root_eq_ordered, OrderIso.apply_symm_apply]

theorem root_eq_original (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool)
    (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    root P F c r = BoundedCriticalSampleFiberRoot.root P F c r := root_eq_ordered P F c r

def finish (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst z))) (pairSnd z)) (pairSnd (pairFst z))
theorem finish_FP : finish ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hk := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hk

noncomputable def signQuery (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNatCode.encode (index P F (pairFst q)))) (pairSnd q)
theorem signQuery_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (signQuery P F) := by
  have E := ((evaluator h A ha).precompose pairFst pairFst_mem_FP).withInput.postcompose finish finish_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, signQuery])

noncomputable def sign (P : Readers) (F : BoundedAlgebraicSlice.Family) : List Bool → List Bool := BoundedCriticalSampleFiberSignatureRead.value P F ∘ signQuery P F
theorem sign_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (sign P F) :=
  (signQuery_evaluator h A ha).chain (BoundedCriticalSampleFiberSignatureRead.evaluator h A ha)

theorem sign_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (r : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) (k : ℕ) :
    sign P F (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        (((Polynomial.derivative^[k]) (BoundedCriticalSampleSlice.specialized P F c)).eval (root P F c r).val)) := by
  simp only [sign, Function.comp_apply, signQuery, pairFst_pair, pairSnd_pair]
  exact BoundedCriticalSampleFiberSignatureRead.derivative_packet P F c
    ⟨index P F (pair c (BinaryNatCode.encode r.val)), (index_spec P F c r).1⟩ k

end LeanCanny.Encoding.BoundedCriticalSampleFiberOrderedRoot
