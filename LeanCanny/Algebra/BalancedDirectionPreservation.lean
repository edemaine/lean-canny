/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedDirectionCorrect

/-! # Direction writes preserve other completed parents in the same layer -/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding
open BalancedParameterContext (packet)
open SeparableBits (Family)

theorem consistent_replace_peer (B : Family) (f : List Bool) (leaves : ℕ → SeparableIntegerPolynomial)
    (n h i j v : ℕ) (hW : 0 < BalancedMetadataTable.width f)
    (hcap : BalancedMetadataTable.capacity n ≤ BalancedMetadataTable.cells f)
    (hv : v < 2 ^ BalancedMetadataTable.width f)
    (hh : h ≤ n.size) (hi : i < 2 ^ (n.size - h)) (hne : i ≠ j)
    (hc : Consistent B f leaves h i) :
    Consistent B (BalancedMetadataTable.replace f (2 * BalancedMetadataTable.key h j + 1) v) leaves h i := by
  cases h with
  | zero => simpa only [Consistent, BalancedMetadataTable.source_replace] using hc
  | succ h =>
    obtain ⟨hcl, hcr, hdl, hdr, hd⟩ := hc
    have hi' := child_index_lt n.size h i hh hi
    have hcell (which : Bool) (k l : ℕ) (hk : k ≤ n.size) (hl : l < 2 ^ (n.size - k)) :=
      (BalancedMetadataTable.cell_lt_capacity which n k l hk hl).trans_le hcap
    refine ⟨consistent_replace_above B f leaves n (h + 1) j v h (2 * i) hW hcap hv (by omega) (by omega) hi'.1 hcl,
      consistent_replace_above B f leaves n (h + 1) j v h (2 * i + 1) hW hcap hv (by omega) (by omega) hi'.2 hcr, ?_, ?_, ?_⟩
    · rw [BalancedMetadataTable.order_replace_direction f (BalancedMetadataTable.key (h + 1) j) v h (2 * i) hW
        (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell false h (2 * i) (by omega) hi'.1) hv]
      exact hdl
    · rw [BalancedMetadataTable.order_replace_direction f (BalancedMetadataTable.key (h + 1) j) v h (2 * i + 1) hW
        (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell false h (2 * i + 1) (by omega) hi'.2) hv]
      exact hdr
    · rw [BalancedMetadataTable.direction_replace_other f (BalancedMetadataTable.key (h + 1) j) v (h + 1) i hW
        (by simpa only [ite_true] using hcell true (h + 1) i hh hi) hv]
      · exact hd
      · intro he
        exact hne (BalancedMetadataTable.key_injective (h + 1) i (h + 1) j he).2

end LeanCanny.Algebra.BalancedTablePolynomials
