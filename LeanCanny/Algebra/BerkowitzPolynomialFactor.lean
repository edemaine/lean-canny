/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPolynomialMoment

/-!
# Coefficients of polynomial Berkowitz factors

The four factor cases select a constant coefficient, a negative diagonal
coefficient, a negative trailing-block moment coefficient, or zero.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower
open Berkowitz
open Polynomial Matrix

theorem moment_value_eq {F : ModularFamily} (p : List Bool)
    (hs : stage F (pairFst p) < F.dimension (pairFst (pairFst p))) :
    (momentFamily F).value p = residueBits
      ((borderMoment (fun j => principalBlock (F.matrix (pairFst (pairFst p))) (stage F (pairFst p)) hs 0 j.succ)
        (fun i => principalBlock (F.matrix (pairFst (pairFst p))) (stage F (pairFst p)) hs i.succ 0)
        ((principalBlock (F.matrix (pairFst (pairFst p))) (stage F (pairFst p)) hs).submatrix Fin.succ Fin.succ)
        (momentExponent F (pairFst p))).coeff (Nat.fromBitsLE (pairSnd p))) := by
  have hr : (momentFamily F).row p =
      fun j => principalBlock (F.matrix (pairFst (pairFst p))) (stage F (pairFst p)) hs 0 j.succ := by
    funext j
    change Fin (F.dimension (pairFst (pairFst p)) - stage F (pairFst p) - 1) at j
    have hv : stage F (pairFst p) + 1 + j.val < F.dimension (pairFst (pairFst p)) := by have h := j.isLt; omega
    change F.matrix (pairFst (pairFst p)) ⟨stage F (pairFst p), hs⟩ ⟨stage F (pairFst p) + 1 + j.val, hv⟩ =
      F.matrix (pairFst (pairFst p)) ⟨stage F (pairFst p), hs⟩ ⟨stage F (pairFst p) + (j.val + 1), by omega⟩
    congr 1
    exact Fin.ext (by omega : stage F (pairFst p) + 1 + j.val = stage F (pairFst p) + (j.val + 1))
  have hc : (momentFamily F).column p =
      fun i => principalBlock (F.matrix (pairFst (pairFst p))) (stage F (pairFst p)) hs i.succ 0 := by
    funext i
    change Fin (F.dimension (pairFst (pairFst p)) - stage F (pairFst p) - 1) at i
    have hv : stage F (pairFst p) + 1 + i.val < F.dimension (pairFst (pairFst p)) := by have h := i.isLt; omega
    change F.matrix (pairFst (pairFst p)) ⟨stage F (pairFst p) + 1 + i.val, hv⟩ ⟨stage F (pairFst p), hs⟩ =
      F.matrix (pairFst (pairFst p)) ⟨stage F (pairFst p) + (i.val + 1), by omega⟩ ⟨stage F (pairFst p), hs⟩
    congr 1
    exact Fin.ext (by omega : stage F (pairFst p) + 1 + i.val = stage F (pairFst p) + (i.val + 1))
  have hA : (momentFamily F).matrix p =
      (principalBlock (F.matrix (pairFst (pairFst p))) (stage F (pairFst p)) hs).submatrix Fin.succ Fin.succ := by
    funext i j
    change Fin (F.dimension (pairFst (pairFst p)) - stage F (pairFst p) - 1) at i j
    have hi : stage F (pairFst p) + 1 + i.val < F.dimension (pairFst (pairFst p)) := by have h := i.isLt; omega
    have hj : stage F (pairFst p) + 1 + j.val < F.dimension (pairFst (pairFst p)) := by have h := j.isLt; omega
    change F.matrix (pairFst (pairFst p)) ⟨stage F (pairFst p) + 1 + i.val, hi⟩
        ⟨stage F (pairFst p) + 1 + j.val, hj⟩ =
      F.matrix (pairFst (pairFst p)) ⟨stage F (pairFst p) + (i.val + 1), by omega⟩
        ⟨stage F (pairFst p) + (j.val + 1), by omega⟩
    congr 1
    · exact Fin.ext (by omega : stage F (pairFst p) + 1 + i.val = stage F (pairFst p) + (i.val + 1))
    · exact Fin.ext (by omega : stage F (pairFst p) + 1 + j.val = stage F (pairFst p) + (j.val + 1))
  change residueBits (((momentFamily F).row p ⬝ᵥ ((momentFamily F).matrix p ^ momentExponent F (pairFst p) *ᵥ
    (momentFamily F).column p)).coeff (Nat.fromBitsLE (pairSnd p))) = _
  rw [hr, hc, hA]
  rfl

end LeanCanny.Algebra.BerkowitzPolynomial.ModularAccess
