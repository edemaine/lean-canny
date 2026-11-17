/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledBoundedSum

/-! # One counting level for uniformly many squared polynomial equations -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped BigOperators

noncomputable def sumSquares {α : Type} {n : α → ℕ}
    {P : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ} {enc : α ↪ List Bool} {a : ℕ}
    (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N D b cutoff : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w i, i < N w → (P w i).totalDegree ≤ D w)
    (hmass : ∀ w i, i < N w → LeanCanny.Algebra.MvMass.mass (P w i) ≤ 2 ^ b w)
    (hcutoff : ∀ w i, i < N w → C.cutoff (w, i) ≤ cutoff w) :
    Controlled (fun w => ∑ i ∈ Finset.range (N w), P w i ^ 2) enc (a + 1) := by
  apply boundedSum (P := fun w i => P w i ^ 2) (C.pow (fun _ => 2) (ComputableInPolyTime.const 2)) E hn
    N (fun w => 2 * D w) (fun w => 2 * b w) cutoff hN
    (ComputableInPolyTime.binary_mul' (.const 2) hD)
    (ComputableInPolyTime.binary_mul' (.const 2) hb) hcut
  · intro w i hi
    exact (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (hdeg w i hi))
  · intro w i hi
    exact (LeanCanny.Algebra.MvMass.pow_le _ _).trans
      ((Nat.pow_le_pow_left (hmass w i hi) 2).trans_eq (by rw [← pow_mul, Nat.mul_comm]))
  · exact hcutoff

end LeanCanny.CountingHierarchy.Controlled
