/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace
public import LeanCanny.Algebra.BivariateDeterminantInteger

/-! # A native symbolic pair coefficient stage

The source polynomial orders are fixed metadata. Their binary size is not
required to be unary. Only original bivariate coefficient readers are inputs;
the matrix entry reader, Kronecker encoding, and determinant evaluator are
derived. A uniform recursive tree scheduler is a separate layer.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTableEntryBits
open Polynomial SymbolicScaledSquarefree SymbolicFixedTable
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

def original (q : List Bool) : List Bool := pairFst (pairFst q)
def modulus (q : List Bool) : List Bool := pairSnd (pairFst q)
def inner (q : List Bool) : List Bool := pairFst (pairSnd q)
def outer (q : List Bool) : List Bool := pairSnd (pairSnd q)

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem inner_FP : inner ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem outer_FP : outer ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

noncomputable def Family.matrix (F : Family) (c : List Bool) :
    Matrix (Fin (F.leftOrder c + F.rightOrder c)) (Fin (F.leftOrder c + F.rightOrder c)) (Polynomial Coefficient) :=
  Polynomial.sylvester (shiftFamily (F.left c) (F.direction c)) ((F.right c).map C) (F.leftOrder c) (F.rightOrder c)

noncomputable def Family.value (F : Family) (q : List Bool) : List Bool :=
  integerResidue ((((cannyResultantWithDegrees (F.left (original q)) (F.right (original q)) (F.direction (original q))
    (F.leftOrder (original q)) (F.rightOrder (original q))).coeff (Nat.fromBitsLE (outer q))).coeff
      (Nat.fromBitsLE (inner q)))) (Nat.fromBitsLE (modulus q) + 1)

def determinantEntryQuery (q : List Bool) : List Bool :=
  pair (pair (original (pairFst q)) (modulus (pairFst q))) (pairSnd q)

theorem determinantEntryQuery_FP : determinantEntryQuery ∈ FP := by
  have ho := mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP original_FP
  have hm := mem_FP_comp (f := pairFst) (g := modulus) pairFst_mem_FP modulus_FP
  exact mem_FP_of_eq (mem_FP_pair (mem_FP_pair ho hm) pairSnd_mem_FP) (fun _ => rfl)

theorem Family.evaluator (F : Family) (E : List Bool → ℕ)
    (hpos : ∀ c, 0 < F.leftOrder c + F.rightOrder c)
    (hleft : ∀ c k, ((F.left c).coeff k).natDegree ≤ E c)
    (hright : ∀ c k, ((F.right c).coeff k).natDegree ≤ E c)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction) (hE : BinaryFn E)
    (L : SpaceFunction (coefficient F.left)) (R : SpaceFunction (coefficient F.right)) : SpaceFunction F.value := by
  let N := fun q => F.leftOrder (original q) + F.rightOrder (original q)
  let P := fun q => F.matrix (original q)
  let b := fun q => BinaryNatCode.encode (E (original q))
  have he := (F.entryEvaluator hm hn hc L R).precompose determinantEntryQuery determinantEntryQuery_FP
  have hN : ∀ q, 0 < N q := fun q => hpos (original q)
  have hP : ∀ q (i j : Fin (N q)) k, ((P q i j).coeff k).natDegree ≤ Nat.fromBitsLE (b q) := by
    intro q i j k
    simp only [b, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact sylvester_inner_degree _ _ _ _ _ _ (hleft (original q)) (hright (original q)) i j k
  have hread : ∀ q (i j : Fin (N q)) u v,
      (F.entry ∘ determinantEntryQuery) (pair q (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
          integerResidue (((P q i j).coeff v).coeff u) (Nat.fromBitsLE (modulus q) + 1) := by
    intro q i j u v
    have h := F.entry_correct (original q) (modulus q) i j u v
    change F.entry _ = integerResidue (((P q i j).coeff v).coeff u) (Nat.fromBitsLE (modulus q) + 1) at h
    simpa only [Function.comp_apply, determinantEntryQuery, pairFst_pair, pairSnd_pair] using h

  have hdim : (fun q => BinaryNatCode.encode (N q)) ∈ FP :=
    mem_FP_comp original_FP (hm.add hn).bits_mem_FP
  have hb : b ∈ FP := mem_FP_comp original_FP hE.bits_mem_FP
  have hd := BivariateDeterminantBits.integerEvaluator N modulus inner outer b P _ hN hP hread he
    hdim modulus_FP inner_FP outer_FP hb
  exact hd.congr (funext fun q => rfl)

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
