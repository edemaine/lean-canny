/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCharacteristicEvaluation
public import LeanCanny.CountingHierarchy.FiniteRelativeCharacteristic

/-! # The relative evaluator computes the actual source characteristic polynomial -/

public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

theorem relativeValue_eq (C : Controlled P enc a) (d : α → ℕ) (w : α) (p : ℕ)
    (z : List ℕ) (hp : p.Prime) (hcut : C.cutoff w < p) (hd : 1 ≤ d w)
    (hP : (P w).totalDegree ≤ d w + 1)
    (hlarge : criticalCoefficientPrimeCutoff (n w) (d w) < p) :
    C.relativeValue d (w, p, z) = evaluation (finiteRelativeCharacteristic (d w) (P w) hP) p z := by
  let : Fact p.Prime := ⟨hp⟩
  let F := MvPolynomial.rename finSumFinEquiv.symm (P w)
  have hF : F.totalDegree ≤ d w + 1 := (MvPolynomial.totalDegree_rename_le _ _).trans hP
  let Q := relativeCharacteristic (d w) F hF
  let phi := relativeParameterEvaluation ((z[1]?.getD 0 : ℕ) : ZMod p)
    (fun i : Fin (m w) => ((z.drop 2)[i.val]?.getD 0 : ZMod p))
  have hc (k : ℕ) (_hk : k ≤ (d w + 1) ^ n w) :
      (zeroCoefficientValue p (n w) (d w) (z[1]?.getD 0) k
        (fun y => C.evaluate (w, p, joinedPoint (n w) (m w) y (z.drop 2))) : ZMod p) = phi (Q.coeff k) := by
    exact C.frozenCoefficient_cast (fun _ => p) d (fun _ => z[1]?.getD 0) (fun _ => k)
      (fun _ => z.drop 2) w hp hcut hd hP hlarge
  have he := binaryPolynomialValue_cast phi Q ((d w + 1) ^ n w) (z[0]?.getD 0)
    (relativeCharacteristic_natDegree (d w) F hF).le _ hc
  have hm : (C.relativeValue d (w, p, z) : ZMod p) =
      MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
        (fun i : Fin (m w + 2) => (z[i.val]?.getD 0 : ZMod p))
        (finiteRelativeCharacteristic (d w) (P w) hP) := by
    rw [eval_finiteRelativeCharacteristic]
    exact he
  have hv := congrArg ZMod.val hm
  simpa only [relativeValue, binaryPolynomialValue, ZMod.val_natCast, Nat.mod_mod,
    evaluation] using hv

end LeanCanny.CountingHierarchy.Controlled
