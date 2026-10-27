/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootRank
public import LeanCanny.Computation.BoundedChoice

/-! # Native conversion from real-order root indices to symbolic labels

Bounded search inverts the native real-order rank. The selected hash ordinal
denotes exactly the root at the requested real-order index, including roots
extraneous to the critical sample system. All selection work is charged.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionOrderedRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

def source (s : List Bool) : List Bool := pairFst (pairFst s)
def rankQuery (s : List Bool) : List Bool := pair (source s) (pairSnd s)
theorem source_FP : source ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem rankQuery_FP : rankQuery ∈ FP := mem_FP_pair source_FP pairSnd_mem_FP

noncomputable def language (P : Readers) : Language := {s |
  Nat.fromBitsLE (pairSnd s) < BoundedProjectionRootCount.count P (source s) ∧
    BoundedProjectionRootRank.value P (rankQuery s) = Nat.fromBitsLE (pairSnd (pairFst s))}

def accept (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    Nat.fromBitsLE (pairSnd (pairSnd z)) = Nat.fromBitsLE (pairSnd (pairFst (pairFst z))))
theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hc := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  have hj := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hN := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact ((hj.lt hN).and (hr.eq hc)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P) := by
  have N := (BoundedProjectionRootCount.evaluator h ha).precompose source source_FP
  have R := (BoundedProjectionRootRank.evaluator h ha).precompose rankQuery rankQuery_FP
  apply (N.pairOutputs R).withInput.decider accept accept_FP
  intro s
  simp only [language, Set.mem_ofPred_eq, accept, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

noncomputable def bound (P : Readers) (u : List Bool) : ℕ := BoundedProjectionRootCount.degree P (pairFst u)
theorem bound_binary {P : Readers} (h : P.PolyTime) : BinaryFn (bound P) :=
  (BoundedProjectionRootCount.degree_binary h).comp pairFst_mem_FP

noncomputable def index (P : Readers) (u : List Bool) : ℕ := BoundedChoice.search (language P) u (bound P u) - 1
theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (index P u)) := by
  have E := BoundedChoice.evaluator (decider h ha) (fun u => BinaryNatCode.encode (bound P u)) (bound_binary h).bits_mem_FP
  exact E.congr (funext fun u => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, index])

attribute [local irreducible] language index

theorem index_spec (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    index P (pair c (BinaryNatCode.encode r.val)) < BoundedProjectionRootCount.count P c ∧
      BoundedProjectionRootRank.value P (pair c (BinaryNatCode.encode (index P (pair c (BinaryNatCode.encode r.val))))) = r.val := by
  obtain ⟨a, ha⟩ := BoundedProjectionRootRank.exists_rank P c r.val r.isLt
  have hN : BoundedProjectionRootCount.count P c ≤ BoundedProjectionRootCount.degree P c :=
    BoundedCriticalLabels.rootSet_card_le P c
  have hex : ∃ j < bound P (pair c (BinaryNatCode.encode r.val)),
      pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode j) ∈ language P := by
    refine ⟨a.val, ?_, ?_⟩
    · simpa only [bound, pairFst_pair] using a.isLt.trans_le hN
    · simp only [language, Set.mem_ofPred_eq, source, rankQuery, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact ⟨a.isLt, (BoundedProjectionRootRank.value_packet P c a).trans ha⟩
  have hw := (BoundedChoice.witness (language P) _ _ hex).2
  unfold index
  simpa only [language, Set.mem_ofPred_eq, source, rankQuery, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits] using hw

noncomputable def root (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    BoundedProjectionRecordSpan.Root P c :=
  BoundedProjectionHashEnumeration.root P c ⟨index P (pair c (BinaryNatCode.encode r.val)), (index_spec P c r).1⟩

theorem root_eq_ordered (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    root P c r = (BoundedCriticalLabels.rootSet P c).orderIsoOfFin (k := BoundedProjectionRootCount.count P c) rfl r := by
  apply ((BoundedCriticalLabels.rootSet P c).orderIsoOfFin (k := BoundedProjectionRootCount.count P c) rfl).symm.injective
  rw [OrderIso.symm_apply_apply]
  apply Fin.ext
  change BoundedProjectionRootOrder.rank P c
    ⟨index P (pair c (BinaryNatCode.encode r.val)), (index_spec P c r).1⟩ = r.val
  rw [← BoundedProjectionRootRank.value_packet]
  exact (index_spec P c r).2

theorem root_strictMono (P : Readers) (c : List Bool) : StrictMono (fun r => (root P c r).val) := by
  intro a b hab
  change (root P c a).val < (root P c b).val
  rw [root_eq_ordered P c a, root_eq_ordered P c b]
  exact ((BoundedCriticalLabels.rootSet P c).orderIsoOfFin (k := BoundedProjectionRootCount.count P c) rfl).strictMono hab

theorem root_surjective (P : Readers) (c : List Bool) : Function.Surjective (root P c) := by
  intro x
  refine ⟨((BoundedCriticalLabels.rootSet P c).orderIsoOfFin (k := BoundedProjectionRootCount.count P c) rfl).symm x, ?_⟩
  rw [root_eq_ordered, OrderIso.apply_symm_apply]

theorem sample_root (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    root P c ⟨BoundedCriticalLabels.rank P c x, BoundedProjectionRootCount.rank_lt_count P c x⟩ =
      BoundedCriticalLabels.projectedRoot P c x := by
  rw [root_eq_ordered]
  exact ((BoundedCriticalLabels.rootSet P c).orderIsoOfFin (k := BoundedProjectionRootCount.count P c) rfl).apply_symm_apply _

def finish (z : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst z))) (pairSnd z)) (pairSnd (pairFst z))
theorem finish_FP : finish ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hk := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_pair hc pairSnd_mem_FP) hk

noncomputable def signQuery (P : Readers) (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (BinaryNatCode.encode (index P (pairFst q)))) (pairSnd q)
theorem signQuery_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (signQuery P) := by
  have E := ((evaluator h ha).precompose pairFst pairFst_mem_FP).withInput.postcompose finish finish_FP
  exact E.congr (funext fun q => by simp only [Function.comp_apply, finish, pairFst_pair, pairSnd_pair, signQuery])

noncomputable def sign (P : Readers) : List Bool → List Bool := BoundedProjectionSignatureRead.value P ∘ signQuery P
theorem sign_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (sign P) :=
  (signQuery_evaluator h ha).chain (BoundedProjectionSignatureRead.evaluator h ha)

theorem sign_packet (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (k : ℕ) :
    sign P (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign
        (((BoundedProjectionThom.polynomial P c k).map (Int.castRingHom ℝ)).eval (root P c r).val)) := by
  simp only [sign, Function.comp_apply, signQuery, pairFst_pair, pairSnd_pair]
  exact BoundedProjectionSignatureRead.derivative_packet P c
    ⟨index P (pair c (BinaryNatCode.encode r.val)), (index_spec P c r).1⟩ k

end LeanCanny.Encoding.BoundedProjectionOrderedRoot
