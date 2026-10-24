/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableEntrySpace
public import LeanCanny.Algebra.CertifiedMatrix

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

theorem Family.evaluator (F : Family) (E : List Bool → ℕ)
    (hpos : ∀ c, 0 < F.leftOrder c + F.rightOrder c)
    (hleft : ∀ c k, ((F.left c).coeff k).natDegree ≤ E c)
    (hright : ∀ c k, ((F.right c).coeff k).natDegree ≤ E c)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction) (hE : BinaryFn E)
    (L : SpaceFunction (coefficient F.left)) (R : SpaceFunction (coefficient F.right)) : SpaceFunction F.value := by
  let A := CertifiedMatrix.determinantReader
    (fun c => F.leftOrder c + F.rightOrder c) E F.matrix hpos (hm.add hn) hE
    (fun c i j k => sylvester_inner_degree _ _ _ _ _ _ (hleft c) (hright c) i j k)
    F.entry (F.entryEvaluator hm hn hc L R) F.entry_correct
  exact A.evaluator.congr (funext fun q => rfl)

end LeanCanny.Algebra.SymbolicFixedTableEntryBits
