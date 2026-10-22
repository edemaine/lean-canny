/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Size
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.NatAbs
public import Mathlib.Tactic.Ring

/-! # Constructive denominator clearing for finite rational families

Use the product of all canonical positive denominators as a common scale. The
cleared value at i is its integer numerator times the product of all other
denominators. No integer division or modular inverse is needed. Uniform binary
component bounds give an explicit bound on the cleared coefficient sizes.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteDenominatorClearing
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scale (q : ι → ℚ) : ℕ := ∏ i, (q i).den

def cleared (q : ι → ℚ) (i : ι) : ℤ :=
  (q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)

omit [DecidableEq ι] in
theorem scale_pos (q : ι → ℚ) : 0 < scale q :=
  Finset.prod_pos (fun i _ => (q i).den_pos)

theorem cast_cleared (q : ι → ℚ) (i : ι) : (cleared q i : ℚ) = (scale q : ℚ) * q i := by
  have hs : (scale q : ℚ) = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℚ) := by
    simp only [scale, Nat.cast_prod]
    exact (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den : ℚ)) (Finset.mem_univ i)).symm
  have hd : ((q i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (q i).den_nz
  have hn : q i * (q i).den = (q i).num := (eq_div_iff hd).mp (q i).num_div_den.symm
  simp only [cleared, Int.cast_mul, Int.cast_prod, Int.cast_natCast, hs]
  rw [← hn]
  ring

theorem cleared_eq_product (q : ι → ℚ) (i : ι) :
    cleared q i = (q i).num * ∏ j, if j = i then 1 else ((q j).den : ℤ) := by
  unfold cleared
  congr 1
  symm
  rw [← Finset.prod_erase_mul Finset.univ (fun j => if j = i then 1 else ((q j).den : ℤ)) (Finset.mem_univ i)]
  simp only [ite_true, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

omit [DecidableEq ι] in
theorem scale_le (q : ι → ℚ) (B : ℕ) (hq : ∀ i, (q i).den ≤ 2 ^ B) :
    scale q ≤ 2 ^ (B * Fintype.card ι) := by
  calc
    _ ≤ ∏ _i : ι, 2 ^ B := Finset.prod_le_prod (fun i _ => hq i)
    _ = 2 ^ (B * Fintype.card ι) := by simp [← pow_mul]

theorem cleared_natAbs_le (q : ι → ℚ) (B : ℕ)
    (hq : ∀ i, (q i).num.natAbs ≤ 2 ^ B ∧ (q i).den ≤ 2 ^ B) (i : ι) :
    (cleared q i).natAbs ≤ 2 ^ (B * Fintype.card ι) := by
  have hc : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hprod : (∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)).natAbs =
      ∏ j ∈ Finset.univ.erase i, (q j).den := by
    change Int.natAbsHom (∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ)) = _
    rw [map_prod]
    simp only [Int.natAbsHom_apply, Int.natAbs_natCast]
  simp only [cleared, Int.natAbs_mul, hprod]
  calc
    _ ≤ 2 ^ B * ∏ _j ∈ Finset.univ.erase i, 2 ^ B :=
      Nat.mul_le_mul (hq i).1 (Finset.prod_le_prod (fun j _ => (hq j).2))
    _ = 2 ^ (B * Fintype.card ι) := by
      simp only [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      rw [← pow_succ', Nat.sub_add_cancel hc, ← pow_mul]

theorem cleared_size_le (q : ι → ℚ) (B : ℕ)
    (hq : ∀ i, (q i).num.natAbs.size ≤ B ∧ (q i).den.size ≤ B) (i : ι) :
    (cleared q i).natAbs.size ≤ B * Fintype.card ι + 1 := by
  have h := cleared_natAbs_le q B (fun j =>
    ⟨(Nat.size_le.mp (hq j).1).le, (Nat.size_le.mp (hq j).2).le⟩) i
  simpa only [Nat.size_pow] using Nat.size_le_size h

omit [DecidableEq ι] in
theorem scale_size_le (q : ι → ℚ) (B : ℕ) (hq : ∀ i, (q i).den.size ≤ B) :
    (scale q).size ≤ B * Fintype.card ι + 1 := by
  have h := scale_le q B (fun i => (Nat.size_le.mp (hq i)).le)
  simpa only [Nat.size_pow] using Nat.size_le_size h

end LeanCanny.Algebra.FiniteDenominatorClearing
