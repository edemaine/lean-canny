/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorRecurrence
public import LeanCanny.Algebra.IntegralDenominatorPassSpace
/-! # Tagged mixed births compile to scalar denominator instructions -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralDenominatorPass
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem repeated_scale_product (v : List ℤ) (r : ℕ) :
    (∏ j ∈ Finset.range (v.length * r), IntegralDenominatorPass.scale v (j / r)) = v.prod ^ r := by
  rw [Finset.prod_range]
  have HE : (∏ ij : Fin v.length × Fin r, IntegralDenominatorPass.scale v ij.1.val) =
      ∏ j : Fin (v.length * r), IntegralDenominatorPass.scale v (j.val / r) := by
    apply Fintype.prod_equiv finProdFinEquiv
    intro ij
    have H := congrArg (fun z : Fin v.length × Fin r => z.1.val) (finProdFinEquiv.symm_apply_apply ij)
    change (finProdFinEquiv ij).val / r = ij.1.val at H
    exact congrArg (IntegralDenominatorPass.scale v) H.symm
  rw [← HE, Fintype.prod_prod_type]
  simp only [Fin.prod_const]
  rw [Finset.prod_pow]
  congr 1
  calc
    (∏ i : Fin v.length, IntegralDenominatorPass.scale v i.val) = ∏ i : Fin v.length, v[i.val] := by
      apply Finset.prod_congr rfl
      intro i _
      unfold IntegralDenominatorPass.scale
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    _ = v.prod := Fin.prod_univ_getElem v

structure Instruction where
  leading : ℤ
  arity : ℕ
  degree : ℕ
  exponent : ℕ
  index : ℕ → ℕ

def Instruction.value (I : Instruction) (v : List ℤ) : ℤ :=
  (I.leading * (∏ j ∈ Finset.range I.arity, IntegralDenominatorPass.scale v (I.index j)) ^ I.degree *
    (I.degree : ℤ)) ^ I.exponent

noncomputable def instruction {n B : ℕ} (P : SpatialSource n) (c : Command n B) (m : ℕ) : Instruction :=
  match c with
  | .integer p _ _ => ⟨p.leadingCoeff, 0, 1, 1, fun _ => 0⟩
  | .critical r => ⟨P.leading * (∏ i, r.scales i) ^ P.degree, m * (n + 1), P.degree, criticalExponent P r, fun j => j / (n + 1)⟩

theorem instruction_value {n B : ℕ} (P : SpatialSource n) (c : Command n B) (m : ℕ) (v : List ℤ) (hv : v.length = m) :
    (instruction P c m).value v = scalarLeading P c v := by
  cases c with
  | integer p _ _ => simp only [instruction, Instruction.value, scalarLeading, Finset.range_zero, Finset.prod_empty, pow_one, Nat.cast_one, mul_one]
  | critical r =>
    change (P.leading * (∏ i, r.scales i) ^ P.degree *
      (∏ j ∈ Finset.range (m * (n + 1)), IntegralDenominatorPass.scale v (j / (n + 1))) ^ P.degree * (P.degree : ℤ)) ^
        criticalExponent P r = criticalDenominator P r v.prod
    rw [← hv, repeated_scale_product]
    unfold criticalDenominator
    rw [mul_pow]
    ring

theorem leading_instruction {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (c : Command n B) :
    IntegralMixedHistoryScript.leading x hm c = (instruction P c m).value (bankList x) := by
  rw [leading_eq, instruction_value P c m (bankList x)]
  exact List.length_ofFn
end LeanCanny.Algebra.IntegralMixedDenominatorBits
