/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotSemantics
public import LeanCanny.ETR.PolynomialMass
/-! # Original sign-slot rows for the spatial producer and clearing boundary

Rows are literal original arithmetic terms, independent of proposed sign
labels. Invalid row indices give zero. Coefficient mass and degree have native
controls derived from original term, before any critical/norm construction.
-/
@[expose] public section
namespace LeanCanny.Encoding.OriginalFormulaRows
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Algebra
open scoped Classical BigOperators

def dimension (c : List Bool) := ClosedFormulaGateMetadata.dimension c
def count (c : List Bool) := ClosedFormulaGateMetadata.count c
def index (q : List Bool) := (pairSnd q).length
def packet (q : List Bool) := pair (pair (pairFst q) []) (pairSnd q)
noncomputable def term (q : List Bool) : Term :=
  if index q < count (pairFst q) then FormulaSignSlotSource.term (packet q) else .const 0

theorem dimension_unary : UnaryFn dimension := ClosedFormulaGateMetadata.dimension_unary
theorem count_unary : UnaryFn count := ClosedFormulaGateMetadata.count_unary
theorem index_unary : UnaryFn index := UnaryFn.length pairSnd_mem_FP

attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count

theorem packet_FP : packet ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (constFn_mem_FP [])) pairSnd_mem_FP

theorem term_FP : (fun q => (term q).toData.toBits) ∈ FP := by
  have HT := mem_FP_comp (f := packet) (g := fun q => (FormulaSignSlotSource.term q).toData.toBits)
    packet_FP FormulaSignSlotSource.term_FP
  apply mem_FP_of_eq ((FPPred.lt index_unary (count_unary.comp pairFst_mem_FP)).ite_mem_FP HT
    (constFn_mem_FP (Term.const 0).toData.toBits))
  intro q
  unfold term
  split_ifs <;> rfl

theorem term_scope (q : List Bool) : (term q).arity≤dimension (pairFst q) := by
  unfold term
  split_ifs
  · simpa only [packet,FormulaSignSlotSource.dimension,pairFst_pair,dimension] using
      FormulaSignSlotSource.term_scope (packet q)
  · exact Nat.zero_le _

theorem term_valid (c : List Bool) (i : ℕ) (hi : i < count c) :
    term (pair c (List.replicate i true))=
      FormulaSignSlotSource.term (pair (pair c []) (List.replicate i true)) := by
  simp only [term,index,packet,pairFst_pair,pairSnd_pair,List.length_replicate,ite_eq_left hi]

theorem term_invalid (c : List Bool) (i : ℕ) (hi : count c ≤ i) :
    term (pair c (List.replicate i true))=.const 0 := by
  simp only [term,index,pairFst_pair,pairSnd_pair,List.length_replicate,ite_eq_right (not_lt.mpr hi)]

theorem label_independent (c label : List Bool) (i : ℕ) (hi : i < count c) :
    term (pair c (List.replicate i true))=
      FormulaSignSlotSource.term (pair (pair c label) (List.replicate i true)) :=
  (term_valid c i hi).trans (FormulaSignSlotSource.term_relabel c [] label _)

noncomputable def mass (c : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (count c), (term (pair c (List.replicate i true))).toData.size
noncomputable def degree (c : List Bool) : ℕ := mass c

attribute [local irreducible] term

theorem mass_unary : UnaryFn mass := by
  have HM : UnaryFn (fun q => (term q).toData.size) :=
    (UnaryFn.length term_FP).of_eq (fun q => Data.length_toBits (term q).toData)
  exact count_unary.sum HM

theorem degree_unary : UnaryFn degree := mass_unary

theorem row_size (c : List Bool) (i : ℕ) (hi : i < count c) :
    (term (pair c (List.replicate i true))).toData.size≤mass c := by
  unfold mass
  exact Finset.single_le_sum (f := fun j => (term (pair c (List.replicate j true))).toData.size)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

noncomputable def polynomial (n : ℕ) (c : List Bool) (i : ℕ) : MvPolynomial (Fin n) ℤ :=
  (term (pair c (List.replicate i true))).finitePolynomial n

theorem polynomial_degree (n : ℕ) (c : List Bool) (i : ℕ) :
    (polynomial n c i).totalDegree≤degree c := by
  by_cases HI : i < count c
  · exact (Term.totalDegree_finitePolynomial _ _).trans
      ((Term.degreeBound_le_dataSize _).trans (row_size c i HI))
  · simp only [polynomial,term_invalid c i (le_of_not_gt HI),Term.finitePolynomial,MvPolynomial.C_0,
      MvPolynomial.totalDegree_zero,Nat.zero_le]

theorem polynomial_mass (n : ℕ) (c : List Bool) (i : ℕ) : MvMass.mass (polynomial n c i)≤2^mass c := by
  by_cases HI : i < count c
  · exact (Term.finitePolynomial_mass _ _).trans (Nat.pow_le_pow_right (by decide) (row_size c i HI))
  · simp only [polynomial,term_invalid c i (le_of_not_gt HI),Term.finitePolynomial,MvPolynomial.C_0,MvMass.zero,Nat.zero_le]

theorem coefficient_bound (n : ℕ) (c : List Bool) (i : ℕ) (a : Fin n →₀ ℕ) :
    ((polynomial n c i).coeff a).natAbs≤2^mass c := (MvMass.coeff_le _ _).trans (polynomial_mass n c i)

theorem eval_polynomial (n : ℕ) (c : List Bool) (i : ℕ) (x : Fin n → ℝ) :
    (polynomial n c i).eval₂ (Int.castRingHom ℝ) x=
      (term (pair c (List.replicate i true))).eval (Formula.extend x) := Term.eval_finitePolynomial _ _ _

end LeanCanny.Encoding.OriginalFormulaRows
