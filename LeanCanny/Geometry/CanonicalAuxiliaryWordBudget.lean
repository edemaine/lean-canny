/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryStepHeight
public import LeanCanny.Geometry.CanonicalAuxiliaryHeightAccess
public import LeanCanny.ETR.FixedLeadingTiltedSourceFP
public import LeanCanny.Computation.PolyTimeBinaryRange
/-! # One native original ceiling covers all recursive tilted LOW terms

The auxiliary term is constructed once. Summing its actual tilted AST sizes
over the original coordinate range yields a native binary bound. Enlarging
the original seed by this sum covers every later frozen-count choice; no
retained-prefix AST-size reader or coefficient evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Computation LeanCanny.ETR

theorem auxiliaryTerm_FP {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    (fun q => (AuxiliaryTiltedTerm.term (n q) (t q)).toData.toBits)∈FP := by
  have HV := mem_FP_of_eq (Term.variableBits_mem_FP hn) (fun q => Term.variableBits_eq (n q))
  refine mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (Codec.taggedTwo_mem_FP 3 ht ht)
    (Codec.taggedTwo_mem_FP 3 HV HV)) (fun q => ?_)
  simp only [AuxiliaryTiltedTerm.term,Term.add_toBits,Term.mul_toBits]

theorem wordBudget_binary {n D : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (hD : UnaryFn D) (ht : (fun q => (t q).toData.toBits)∈FP)
    (hb : ∀ q, (AuxiliaryTiltedTerm.term (n q) (t q)).degreeBound≤D q) :
    BinaryFn (fun q => wordBudget (n q) (D q) (t q)) := by
  have HT := auxiliaryTerm_FP hn ht
  have HA : (fun z => (AuxiliaryTiltedTerm.term (n (pairFst z)) (t (pairFst z))).toData.toBits)∈FP :=
    mem_FP_comp pairFst_mem_FP HT
  have HW := FixedLeadingTiltedSourceFP.lowTerm_FP HA (UnaryFn.length pairSnd_mem_FP)
    (hD.comp pairFst_mem_FP) (hn.comp pairFst_mem_FP) (fun z => hb (pairFst z))
  have HS : UnaryFn (fun z =>
      (FixedLeadingTiltedSource.lowTerm (pairSnd z).length (D (pairFst z)) (n (pairFst z))
        (AuxiliaryTiltedTerm.term (n (pairFst z)) (t (pairFst z)))).toData.size) :=
    (UnaryFn.length HW).of_eq (fun z => Data.length_toBits _)
  apply BinaryFn.of_eq (BinaryFn.sum (hn.add (UnaryFn.const 1)) (BinaryFn.ofUnary HS))
  intro q
  simp only [pairFst_pair,pairSnd_pair,List.length_replicate]
  rw [wordBudget]
  exact (Fin.sum_univ_eq_sum_range (fun k =>
    (FixedLeadingTiltedSource.lowTerm k (D q) (n q)
      (AuxiliaryTiltedTerm.term (n q) (t q))).toData.size) (n q+1)).symm

theorem augmentedDegree_unary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    UnaryFn (fun q => (AuxiliaryTiltedTerm.term (n q) (t q)).toData.size) :=
  (UnaryFn.length (auxiliaryTerm_FP hn ht)).of_eq
    (fun q => Data.length_toBits (AuxiliaryTiltedTerm.term (n q) (t q)).toData)

theorem originalWordBudget_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits)∈FP) :
    BinaryFn (fun q => wordBudget (n q) (AuxiliaryTiltedTerm.term (n q) (t q)).toData.size (t q)) :=
  wordBudget_binary hn (augmentedDegree_unary hn ht) ht (fun q => (AuxiliaryTiltedTerm.term (n q) (t q)).degreeBound_le_dataSize)

def originalSeed (n D C : ℕ) (t : Term) : ℕ := C+wordBudget n D t

theorem originalSeed_binary {n D C : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (hD : UnaryFn D) (hC : BinaryFn C) (ht : (fun q => (t q).toData.toBits)∈FP)
    (hb : ∀ q, (AuxiliaryTiltedTerm.term (n q) (t q)).degreeBound≤D q) :
    BinaryFn (fun q => originalSeed (n q) (D q) (C q) (t q)) :=
  hC.add (wordBudget_binary hn hD ht hb)

theorem word_le_originalSeed (n k D C : ℕ) (t : Term) (hk : k≤n) :
    (FixedLeadingTiltedSource.lowTerm k D (Fin.last n).val (AuxiliaryTiltedTerm.term n t)).toData.size≤
      originalSeed n D C t :=
  (word_le_budget n k D t hk).trans (Nat.le_add_left _ _)

theorem word_le_recursiveHeight (n k S B D C j : ℕ) (t : Term) (hk : k≤n) :
    (FixedLeadingTiltedSource.lowTerm k D (Fin.last n).val (AuxiliaryTiltedTerm.term n t)).toData.size≤
      recursiveHeight n S B D (originalSeed n D C t) j :=
  ((word_le_originalSeed n k D C t hk).trans (Nat.le_succ _)).trans
    (seed_le_recursiveHeight n S B D (originalSeed n D C t) j)

theorem seededHeight_binary {n S B D C j : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (hS : UnaryFn S) (hB : UnaryFn B) (hD : UnaryFn D) (hC : BinaryFn C) (hj : UnaryFn j)
    (ht : (fun q => (t q).toData.toBits)∈FP)
    (hb : ∀ q, (AuxiliaryTiltedTerm.term (n q) (t q)).degreeBound≤D q) :
    BinaryFn (fun q => recursiveHeight (n q) (S q) (B q) (D q)
      (originalSeed (n q) (D q) (C q) (t q)) (j q)) :=
  recursiveHeight_binary hn hS hB (BinaryFn.ofUnary hD) (originalSeed_binary hn hD hC ht hb) hj

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
