/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.BalancedTablePolynomials

/-! # Locality of balanced integer trees and supplied-table consistency -/
@[expose] public section
namespace LeanCanny.Algebra.BalancedSubtreeLocality
open scoped Classical

private theorem left_interval (h i j : ℕ) : 2^h*(2*i)+j=2^(h+1)*i+j := by
  rw [pow_succ]
  ring
private theorem right_interval (h i j : ℕ) : 2^h*(2*i+1)+j=2^(h+1)*i+(2^h+j) := by
  rw [pow_succ]
  ring

/-- The polynomial at a node only depends on its finite leaf interval. -/
theorem node_polynomial_congr (a b : ℕ → SeparableIntegerPolynomial) (h i : ℕ)
    (he : ∀ j<2^h, (a (2^h*i+j)).polynomial=(b (2^h*i+j)).polynomial) :
    (BalancedPrimitiveTree.node a h i).polynomial=(BalancedPrimitiveTree.node b h i).polynomial := by
  induction h generalizing i with
  | zero => simpa only [BalancedPrimitiveTree.node, pow_zero, one_mul, Nat.add_zero] using he 0 (by decide)
  | succ h ih =>
    have hl := ih (2*i) (fun j hj => by
      rw [left_interval]
      exact he j (hj.trans_le (Nat.pow_le_pow_right (by decide) (by omega))))
    have hr := ih (2*i+1) (fun j hj => by
      rw [right_interval]
      exact he (2^h+j) (by rw [pow_succ]; omega))
    simp only [BalancedPrimitiveTree.node, SeparableIntegerPolynomial.combine]
    rw [hl, hr]

/-- Full consistency contains every leftmost lower subtree. -/
theorem consistent_lower_zero (B : SeparableBits.Family) (c : List Bool)
    (a : ℕ → SeparableIntegerPolynomial) (H h : ℕ) (hh : h≤H)
    (hc : BalancedTablePolynomials.Consistent B c a H 0) :
    BalancedTablePolynomials.Consistent B c a h 0 := by
  induction H with
  | zero =>
    have he : h=0 := by omega
    subst h
    exact hc
  | succ H ih =>
    by_cases he : h=H+1
    · subst h; exact hc
    · have hl : BalancedTablePolynomials.Consistent B c a H 0 := by
        simpa only [Nat.mul_zero] using hc.1
      exact ih (by omega) hl

/-- Descendant consistency follows by selecting the appropriate child at each
level, retaining the original global leaf indices. -/
theorem consistent_descendant (B : SeparableBits.Family) (c : List Bool)
    (a : ℕ → SeparableIntegerPolynomial) (h k r j : ℕ) (hj : j<2^k)
    (hc : BalancedTablePolynomials.Consistent B c a (h+k) r) :
    BalancedTablePolynomials.Consistent B c a h (2^k*r+j) := by
  induction k generalizing r j with
  | zero =>
    have he : j=0 := by simp only [pow_zero] at hj; omega
    subst j
    simpa only [Nat.add_zero, pow_zero, one_mul] using hc
  | succ k ih =>
    have hcs : BalancedTablePolynomials.Consistent B c a ((h+k)+1) r := by
      simpa only [Nat.add_assoc] using hc
    by_cases hl : j<2^k
    · have H := ih (2*r) j hl hcs.1
      have he : 2^k*(2*r)+j=2^(k+1)*r+j := by rw [pow_succ]; ring
      simpa only [he] using H
    · have hr : j-2^k<2^k := by rw [pow_succ] at hj; omega
      have H := ih (2*r+1) (j-2^k) hr hcs.2.1
      have he : 2^k*(2*r+1)+(j-2^k)=2^(k+1)*r+j := by
        rw [pow_succ]
        have hs : 2^k+(j-2^k)=j := Nat.add_sub_of_le (by omega)
        calc
          _ = (2^k*(r*2))+(2^k+(j-2^k)) := by ring
          _ = _ := by rw [hs]; ring
      simpa only [he] using H

theorem consistent_subtree (B : SeparableBits.Family) (c : List Bool)
    (a : ℕ → SeparableIntegerPolynomial) (H h i : ℕ) (hh : h≤H) (hi : i<2^(H-h))
    (hc : BalancedTablePolynomials.Consistent B c a H 0) :
    BalancedTablePolynomials.Consistent B c a h i := by
  have hcs : BalancedTablePolynomials.Consistent B c a (h+(H-h)) 0 := by
    rw [Nat.add_sub_of_le hh]
    exact hc
  simpa only [Nat.mul_zero, Nat.zero_add] using consistent_descendant B c a h (H-h) 0 i hi hcs

/-- A node's leaf interval stays inside the enclosing balanced tree. -/
theorem interval_index_lt (H h i j : ℕ) (hh : h ≤ H)
    (hi : i < 2 ^ (H - h)) (hj : j < 2 ^ h) : 2 ^ h * i + j < 2 ^ H := by
  have hp : 2 ^ h * 2 ^ (H - h) = 2 ^ H := by
    rw [← pow_add, Nat.add_sub_of_le hh]
  have hx : 2 ^ h * i + j < 2 ^ h * (i + 1) := by nlinarith
  exact hx.trans_le ((Nat.mul_le_mul_left (2 ^ h) (Nat.succ_le_of_lt hi)).trans_eq hp)

theorem index_lt_of_interval (H h i : ℕ) (hh : h ≤ H)
    (hi : 2 ^ h * (i + 1) ≤ 2 ^ H) : i < 2 ^ (H - h) := by
  have hp : 2 ^ h * 2 ^ (H - h) = 2 ^ H := by
    rw [← pow_add, Nat.add_sub_of_le hh]
  by_contra hn
  have hm := Nat.mul_le_mul_left (2 ^ h) (show 2 ^ (H - h) ≤ i by omega)
  have hz := Nat.two_pow_pos h
  rw [← hp] at hi
  nlinarith

theorem ancestor_lt (H h j : ℕ) (hh : h ≤ H) (hj : j < 2 ^ H) :
    j / 2 ^ h < 2 ^ (H - h) := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).mpr
  calc
    j < 2 ^ H := hj
    _ = 2 ^ (H - h) * 2 ^ h := by rw [← pow_add, Nat.sub_add_cancel hh]

/-- Orders are stored at a node's parent. Thus a strict descendant has exact
order metadata, including the root of any strictly smaller retained subtree. -/
theorem order_eq_node_degree (B : SeparableBits.Family) (c : List Bool)
    (a : ℕ → SeparableIntegerPolynomial) (H h i : ℕ) (hh : h < H)
    (hi : i < 2 ^ (H - h)) (hc : BalancedTablePolynomials.Consistent B c a H 0) :
    BalancedMetadataTable.order (BalancedParameterContext.packet c h i) =
      (BalancedPrimitiveTree.node a h i).polynomial.natDegree := by
  have hp : i / 2 < 2 ^ (H - (h + 1)) := by
    have he : H - h = (H - (h + 1)) + 1 := by omega
    rw [he, pow_succ] at hi
    omega
  have hs := consistent_subtree B c a H (h + 1) (i / 2) (by omega) hp hc
  by_cases he : i % 2 = 0
  · have hi0 : 2 * (i / 2) = i := by have hm := Nat.mod_add_div i 2; omega
    simpa only [hi0] using hs.2.2.1
  · have hi1 : 2 * (i / 2) + 1 = i := by
      have hm := Nat.mod_add_div i 2
      have hb := Nat.mod_lt i (by decide : 0 < 2)
      omega
    simpa only [hi1] using hs.2.2.2.1

/-- Replacing unused leaves preserves all finite consistency conditions. -/
theorem consistent_congr (B : SeparableBits.Family) (c : List Bool)
    (a b : ℕ → SeparableIntegerPolynomial) (h i : ℕ)
    (he : ∀ j<2^h, (a (2^h*i+j)).polynomial=(b (2^h*i+j)).polynomial)
    (hc : BalancedTablePolynomials.Consistent B c a h i) :
    BalancedTablePolynomials.Consistent B c b h i := by
  induction h generalizing i with
  | zero =>
    have hx := he 0 (by decide)
    simp only [pow_zero, one_mul, Nat.add_zero] at hx
    exact hc.trans hx
  | succ h ih =>
    have hl (j : ℕ) (hj : j<2^h) : (a (2^h*(2*i)+j)).polynomial=(b (2^h*(2*i)+j)).polynomial := by
      rw [left_interval]
      exact he j (hj.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    have hr (j : ℕ) (hj : j<2^h) : (a (2^h*(2*i+1)+j)).polynomial=(b (2^h*(2*i+1)+j)).polynomial := by
      rw [right_interval]
      exact he (2^h+j) (by rw [pow_succ]; omega)
    obtain ⟨hcl,hcr,hdl,hdr,hd⟩ := hc
    refine ⟨ih _ hl hcl, ih _ hr hcr, ?_, ?_, ?_⟩
    · rw [← node_polynomial_congr a b h (2*i) hl]; exact hdl
    · rw [← node_polynomial_congr a b h (2*i+1) hr]; exact hdr
    · rw [← node_polynomial_congr a b h (2*i) hl, ← node_polynomial_congr a b h (2*i+1) hr]
      exact hd

end LeanCanny.Algebra.BalancedSubtreeLocality
