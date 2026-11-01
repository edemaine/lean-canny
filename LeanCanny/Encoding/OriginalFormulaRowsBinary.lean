/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.OriginalFormulaRowsFamily
/-! # Native binary row selectors retain exact invalid-index zero semantics -/
@[expose] public section
namespace LeanCanny.Encoding.OriginalFormulaRows
open ETR LeanCanny.Computation
open scoped Classical

def binaryPacket (q : List Bool) : List Bool := pair (pairFst q)
  (List.replicate (min (Nat.fromBitsLE (pairSnd q)) (count (pairFst q))) true)
noncomputable def binaryTerm (q : List Bool) : Term := term (binaryPacket q)

theorem binaryPacket_FP : binaryPacket ∈ FP :=
  mem_FP_pair pairFst_mem_FP (UnaryFn.fromBitsLE_min pairSnd_mem_FP (count_unary.comp pairFst_mem_FP)).mem_FP

theorem binaryTerm_FP : (fun q => (binaryTerm q).toData.toBits) ∈ FP := by
  unfold binaryTerm
  exact mem_FP_comp (f := binaryPacket) (g := fun q => (term q).toData.toBits) binaryPacket_FP term_FP

theorem binaryTerm_indexed (c : List Bool) (i : ℕ) :
    binaryTerm (pair c (BinaryNatCode.encode i))=term (pair c (List.replicate i true)) := by
  simp only [binaryTerm,binaryPacket,pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  by_cases HI : i < count c
  · rw [min_eq_left HI.le]
  · have HE : count c ≤ i := le_of_not_gt HI
    rw [min_eq_right HE,term_invalid c (count c) (le_refl _),term_invalid c i HE]

theorem binaryTerm_scope (q : List Bool) : (binaryTerm q).arity≤dimension (pairFst q) := by
  simpa only [binaryTerm,binaryPacket,pairFst_pair] using term_scope (binaryPacket q)

theorem binaryTerm_degree (c : List Bool) (i : ℕ) (n : ℕ) :
    ((binaryTerm (pair c (BinaryNatCode.encode i))).finitePolynomial n).totalDegree≤degree c := by
  rw [binaryTerm_indexed]
  exact polynomial_degree n c i

theorem binaryTerm_mass (c : List Bool) (i : ℕ) (n : ℕ) :
    LeanCanny.Algebra.MvMass.mass ((binaryTerm (pair c (BinaryNatCode.encode i))).finitePolynomial n)≤2^mass c := by
  rw [binaryTerm_indexed]
  exact polynomial_mass n c i

end LeanCanny.Encoding.OriginalFormulaRows
