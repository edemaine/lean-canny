/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ControlledNormComputability

/-! # A Boolean negative-norm test at the source-plus-twenty-four level -/

public section

namespace LeanCanny.CountingHierarchy

lemma int_sign_negative_iff (z : ℤ) : z.sign < 0 ↔ z < 0 := by
  cases z with
  | ofNat n =>
    cases n with
    | zero => decide
    | succ n => simp [Int.sign]; omega
  | negSucc n => simp [Int.sign]

namespace Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

variable {α : Type} {n : α → ℕ} {P : (w : α) → MvPolynomial (Fin (n w)) ℤ}
  {enc : α ↪ List Bool} {a : ℕ}

theorem normNegative_mem (C : Controlled P enc a) (E : Decoder enc) {d : α → ℕ}
    (hdpos : ∀ w, 1 ≤ d w) (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1)
    {data : α → List (ℕ × ℕ)} {e : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (he : ComputableInPolyTime e enc encNat) :
    (fun w => decide (C.normInteger d hdeg data e w < 0)) ∈ CountingFunction (a + 24) enc encBool := by
  have hsign := C.normSign_mem E hdpos hdeg hd hdata he
  have htest : ComputableInPolyTime (fun z : ℤ => decide (z < 0)) encIntBin encBool := by fun_prop
  have hnative := CountingFunction.map hsign htest
  convert hnative using 1
  funext w
  simp only [int_sign_negative_iff]

end Controlled
end LeanCanny.CountingHierarchy
