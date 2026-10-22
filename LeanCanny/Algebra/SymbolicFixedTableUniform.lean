/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicFixedTableSemantics
public import LeanCanny.Algebra.FiniteAnnihilatorHeight

/-! # A native polynomial-time reference exponent for every admissible table

A fixed sixteenth power bounds a squarefree or pair step. The balanced depth
turns that envelope into a power with exponent polynomial in the family count.
Thus the common ordinary-evaluation reference has a native binary FP writer.
-/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicFixedTable
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical BigOperators

def Budget.BoundedBy (B : Budget) (T : ℕ) : Prop :=
  B.degree ≤ T ∧ B.innerDegree ≤ T ∧ B.massExponent ≤ T

theorem gcdMassExponent_uniform (T : ℕ) (hT : 4 ≤ T) : gcdMassExponent T T ≤ T ^ 4 := by
  have hr : gcdMassExponent T T ≤ 8 * T ^ 2 := by
    unfold gcdMassExponent
    calc
      _ ≤ (2 * T) * (2 * T) + (2 * T) * (T + T) := by
        gcongr <;> exact Nat.size_le_self _
      _ = _ := by ring
  exact (hr.trans (by omega : 8 * T ^ 2 ≤ 16 * T ^ 2)).trans
    (CannyResultantBits.sixteen_mul_pow_le T 2 hT)

theorem squarefreeMassExponent_uniform (T : ℕ) (hT : 4 ≤ T) :
    SymbolicScaledSquarefree.massExponent T T ≤ T ^ 7 := by
  have hg := gcdMassExponent_uniform T hT
  have hr : SymbolicScaledSquarefree.massExponent T T ≤ 2 * T ^ 5 + 6 * T ^ 2 := by
    unfold SymbolicScaledSquarefree.massExponent
    calc
      _ ≤ (T + T) * (T + T) + (T + T) * (T ^ 4 + T) := by
        gcongr
        · exact (Nat.size_le_self _).trans (by omega)
        · omega
        · omega
      _ = _ := by ring
  have h2 : T ^ 2 ≤ T ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (hr.trans (by omega : 2 * T ^ 5 + 6 * T ^ 2 ≤ 16 * T ^ 5)).trans
    (CannyResultantBits.sixteen_mul_pow_le T 5 hT)

theorem resultantMassExponent_uniform (T : ℕ) (hT : 4 ≤ T) :
    resultantMassExponent T T (T ^ 4) T T ≤ T ^ 10 := by
  have hr : resultantMassExponent T T (T ^ 4) T T ≤
      2 * CannyResultantBits.coefficientBudget T T (T ^ 4) T T := by
    unfold resultantMassExponent shiftExponent CannyResultantBits.coefficientBudget
    nlinarith
  have hc := CannyResultantBits.coefficientBudget_uniform T hT
  exact (hr.trans (Nat.mul_le_mul_left 2 hc)).trans
    ((by omega : 2 * T ^ 8 ≤ 16 * T ^ 8).trans (CannyResultantBits.sixteen_mul_pow_le T 8 hT))

theorem Budget.squarefree_bounded (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) :
    B.squarefree.BoundedBy (T ^ 16) := by
  have hD := hB.1
  have hE := hB.2.1
  have h1 : T ≤ T ^ 16 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 16 by decide)
  have hi : B.squarefree.innerDegree ≤ 6 * T ^ 3 := by
    change (B.degree + 1) * ((2 * B.degree + 1) * B.innerDegree) ≤ _
    calc
      _ ≤ (2 * T) * ((3 * T) * T) := by gcongr <;> omega
      _ = _ := by ring
  have him : 6 * T ^ 3 ≤ T ^ 16 :=
    (by omega : 6 * T ^ 3 ≤ 16 * T ^ 3).trans
      ((CannyResultantBits.sixteen_mul_pow_le T 3 hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))
  exact ⟨hB.1.trans h1, hi.trans him,
    (squarefreeMassExponent_mono hB.1 hB.2.2).trans
      ((squarefreeMassExponent_uniform T hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))⟩

theorem Budget.pair_bounded (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) :
    B.pair.BoundedBy (T ^ 16) := by
  have h2 : T ^ 2 ≤ T ^ 16 := Nat.pow_le_pow_right (by omega) (by decide)
  have hi : B.pair.innerDegree ≤ 4 * T ^ 2 := by
    change (B.degree + B.degree) * (B.innerDegree + B.innerDegree) ≤ _
    calc
      _ ≤ (T + T) * (T + T) := Nat.mul_le_mul (Nat.add_le_add hB.1 hB.1) (Nat.add_le_add hB.2.1 hB.2.1)
      _ = _ := by ring
  have him : 4 * T ^ 2 ≤ T ^ 16 :=
    (by omega : 4 * T ^ 2 ≤ 16 * T ^ 2).trans
      ((CannyResultantBits.sixteen_mul_pow_le T 2 hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))
  have hc : B.directionLimit ≤ T ^ 4 := by
    change (B.degree * B.degree) ^ 2 ≤ _
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul hB.1 hB.1) 2).trans_eq (by ring)
  exact ⟨(Nat.mul_le_mul hB.1 hB.1).trans (by simpa only [pow_two] using h2), hi.trans him,
    (resultantMassExponent_mono hB.1 hB.1 hc hB.2.2 hB.2.2).trans
      ((resultantMassExponent_uniform T hT).trans (Nat.pow_le_pow_right (by omega) (by decide)))⟩

theorem Budget.testExponent_uniform (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) :
    B.testExponent ≤ T ^ 6 := by
  have hb := hB.2.2
  have hg := (gcdMassExponent_mono hB.1 hB.2.2).trans (gcdMassExponent_uniform T hT)
  have h1 : T ≤ T ^ 4 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 4 by decide)
  have h0 : 1 ≤ T ^ 4 := Nat.one_le_pow _ _ (by omega)
  exact (by unfold Budget.testExponent; omega : B.testExponent ≤ 16 * T ^ 4).trans
    (CannyResultantBits.sixteen_mul_pow_le T 4 hT)

theorem treeBudget_bounded (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) (h : ℕ) :
    (treeBudget B h).BoundedBy (T ^ (16 ^ h)) := by
  induction h with
  | zero => simpa only [treeBudget, pow_zero, pow_one] using hB
  | succ h ih =>
    have ht : T ≤ T ^ (16 ^ h) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := T) (by omega) (Nat.one_le_pow h 16 (by decide))
    have hb := Budget.pair_bounded _ _ (hT.trans ht) ih
    simpa only [treeBudget, ← pow_mul, pow_succ (16 : ℕ) h] using hb

theorem referenceExponent_uniform (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) (h : ℕ) :
    referenceExponent B h ≤ T ^ (16 ^ (h + 1)) := by
  induction h with
  | zero =>
    simpa only [referenceExponent, Finset.sum_range_one, treeBudget, Nat.zero_add, pow_one] using
      (B.testExponent_uniform T hT hB).trans (Nat.pow_le_pow_right (by omega) (show 6 ≤ 16 by decide))
  | succ h ih =>
    have ht : T ≤ T ^ (16 ^ (h + 1)) := by
      simpa only [pow_one] using Nat.pow_le_pow_right (n := T) (by omega) (Nat.one_le_pow (h + 1) 16 (by decide))
    have hb := Budget.testExponent_uniform _ _ (hT.trans ht) (treeBudget_bounded B T hT hB (h + 1))
    rw [← pow_mul] at hb
    have hsmall : T ^ (16 ^ (h + 1)) ≤ T ^ ((16 ^ (h + 1)) * 6) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hstep : 16 * T ^ ((16 ^ (h + 1)) * 6) ≤ T ^ (16 ^ (h + 1 + 1)) := by
      apply (CannyResultantBits.sixteen_mul_pow_le T _ hT).trans
      apply Nat.pow_le_pow_right (by omega)
      rw [pow_succ]
      have hp : 1 ≤ 16 ^ (h + 1) := Nat.one_le_pow _ _ (by decide)
      omega
    unfold referenceExponent at ih ⊢
    rw [Finset.sum_range_succ]
    exact (Nat.add_le_add ih hb).trans ((by omega :
      T ^ (16 ^ (h + 1)) + T ^ ((16 ^ (h + 1)) * 6) ≤ 16 * T ^ ((16 ^ (h + 1)) * 6)).trans hstep)

theorem preparationExponent_uniform (B : Budget) (T : ℕ) (hT : 4 ≤ T) (hB : B.BoundedBy T) (h : ℕ) :
    preparationExponent B h ≤ T ^ (16 ^ (h + 3)) := by
  have hs := B.squarefree_bounded T hT hB
  have ht : T ≤ T ^ 16 := by simpa using Nat.pow_le_pow_right (n := T) (by omega) (show 1 ≤ 16 by decide)
  have hr := referenceExponent_uniform B.squarefree (T ^ 16) (hT.trans ht) hs h
  have heq : 16 * 16 ^ (h + 1) = 16 ^ (h + 2) := by rw [show h + 2 = (h + 1) + 1 by omega, pow_succ]; omega
  rw [← pow_mul, heq] at hr
  have hb := B.testExponent_uniform T hT hB
  have hsmall : T ^ 6 ≤ T ^ (16 ^ (h + 2)) := by
    apply Nat.pow_le_pow_right (by omega)
    have h := Nat.pow_le_pow_right (n := 16) (by decide) (show 1 ≤ h + 2 by omega)
    simpa only [pow_one] using (show 6 ≤ 16 by decide).trans h
  have hstep : 16 * T ^ (16 ^ (h + 2)) ≤ T ^ (16 ^ (h + 3)) := by
    apply (CannyResultantBits.sixteen_mul_pow_le T _ hT).trans
    apply Nat.pow_le_pow_right (by omega)
    rw [show h + 3 = (h + 2) + 1 by omega, pow_succ]
    have hp : 1 ≤ 16 ^ (h + 2) := Nat.one_le_pow _ _ (by decide)
    omega
  exact (Nat.add_le_add hb hr).trans ((by omega :
    T ^ 6 + T ^ (16 ^ (h + 2)) ≤ 16 * T ^ (16 ^ (h + 2))).trans hstep)

def sourceExponent (D E b n : ℕ) : ℕ := (D + E + b + 4) ^ (65536 * (n + 1) ^ 4)

theorem sourceExponent_binary {D E b n : List Bool → ℕ}
    (hD : BinaryFn D) (hE : BinaryFn E) (hb : BinaryFn b) (hn : UnaryFn n) :
    BinaryFn (fun c => sourceExponent (D c) (E c) (b c) (n c)) :=
  (((hD.add hE).add hb).add (BinaryFn.const 4)).powUnary
    ((UnaryFn.const 65536).mul ((hn.add (UnaryFn.const 1)).pow_const 4))

theorem preparationExponent_le_source (B : Budget) (n : ℕ) :
    preparationExponent B n.size ≤ sourceExponent B.degree B.innerDegree B.massExponent n := by
  let T := B.degree + B.innerDegree + B.massExponent + 4
  have hT : 4 ≤ T := by dsimp [T]; omega
  have hb : B.BoundedBy T := by dsimp [Budget.BoundedBy, T]; omega
  apply (preparationExponent_uniform B T hT hb n.size).trans
  apply Nat.pow_le_pow_right (by omega)
  calc
    _ = 16 ^ (n.size + 1) * 256 := by
      rw [show n.size + 3 = (n.size + 1) + 2 by omega, pow_add]; norm_num
    _ ≤ (256 * (n + 1) ^ 4) * 256 :=
      Nat.mul_le_mul_right _ (FiniteAnnihilatorTree.heightExponent_le n)
    _ = _ := by ring

end LeanCanny.Algebra.SymbolicFixedTable
