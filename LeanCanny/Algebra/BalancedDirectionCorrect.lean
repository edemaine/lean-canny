/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedDirectionUpdate

/-! # Correctness of one bottom-up direction-table step

A direction write above a consistent subtree preserves its consistency.
Consequently, scanning and writing a parent whose children are prepared
extends consistency to that parent. The remaining numerical promises are
local child coefficient bounds and enough width for the canonical direction.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials
open LeanCanny.Encoding
open BalancedParameterContext (packet child)
open SeparableBits (Family)

theorem child_index_lt (N h i : ℕ) (hh : h + 1 ≤ N) (hi : i < 2 ^ (N - (h + 1))) :
    2 * i < 2 ^ (N - h) ∧ 2 * i + 1 < 2 ^ (N - h) := by
  have he : N - h = N - (h + 1) + 1 := by omega
  rw [he, pow_succ]
  omega

theorem consistent_replace_above (B : Family) (f : List Bool) (leaves : ℕ → SeparableIntegerPolynomial)
    (n r j v h i : ℕ) (hW : 0 < BalancedMetadataTable.width f)
    (hcap : BalancedMetadataTable.capacity n ≤ BalancedMetadataTable.cells f)
    (hv : v < 2 ^ BalancedMetadataTable.width f)
    (hhr : h < r) (hh : h ≤ n.size) (hi : i < 2 ^ (n.size - h))
    (hc : Consistent B f leaves h i) :
    Consistent B (BalancedMetadataTable.replace f (2 * BalancedMetadataTable.key r j + 1) v) leaves h i := by
  induction h generalizing i with
  | zero => simpa only [Consistent, BalancedMetadataTable.source_replace] using hc
  | succ h ih =>
    obtain ⟨hcl, hcr, hdl, hdr, hd⟩ := hc
    have hi' := child_index_lt n.size h i hh hi
    have hcell (which : Bool) (k l : ℕ) (hk : k ≤ n.size) (hl : l < 2 ^ (n.size - k)) :=
      (BalancedMetadataTable.cell_lt_capacity which n k l hk hl).trans_le hcap
    refine ⟨ih _ (by omega) (by omega) hi'.1 hcl, ih _ (by omega) (by omega) hi'.2 hcr, ?_, ?_, ?_⟩
    · rw [BalancedMetadataTable.order_replace_direction f (BalancedMetadataTable.key r j) v h (2 * i)
        hW (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell false h (2 * i) (by omega) hi'.1) hv]
      exact hdl
    · rw [BalancedMetadataTable.order_replace_direction f (BalancedMetadataTable.key r j) v h (2 * i + 1)
        hW (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell false h (2 * i + 1) (by omega) hi'.2) hv]
      exact hdr
    · rw [BalancedMetadataTable.direction_replace_other f (BalancedMetadataTable.key r j) v (h + 1) i hW
        (by simpa only [ite_true] using hcell true (h + 1) i hh hi) hv]
      · exact hd
      · intro he
        have he' := BalancedMetadataTable.key_injective (h + 1) i r j he
        omega

namespace Candidate

attribute [local irreducible] tree node BinaryNat.normalize BalancedMetadataTable.read

theorem update_consistent (B : Family) (H : List Bool → ℕ) (f : List Bool)
    (leaves : ℕ → SeparableIntegerPolynomial) (n h i : ℕ)
    (hW : 0 < BalancedMetadataTable.width f)
    (hcap : BalancedMetadataTable.capacity n ≤ BalancedMetadataTable.cells f)
    (hh : h + 1 ≤ n.size) (hi : i < 2 ^ (n.size - (h + 1)))
    (hcl : Consistent B f leaves h (2 * i)) (hcr : Consistent B f leaves h (2 * i + 1))
    (hdl : BalancedMetadataTable.order (packet f h (2 * i)) = (BalancedPrimitiveTree.node leaves h (2 * i)).polynomial.natDegree)
    (hdr : BalancedMetadataTable.order (packet f h (2 * i + 1)) = (BalancedPrimitiveTree.node leaves h (2 * i + 1)).polynomial.natDegree)
    (hbl : ∀ k, ((node B (child false (packet f (h + 1) i))).coeff k).natAbs ≤ 2 ^ H (packet f (h + 1) i))
    (hbr : ∀ k, ((node B (child true (packet f (h + 1) i))).coeff k).natAbs ≤ 2 ^ H (packet f (h + 1) i))
    (hfit : PrimitivePair.select (BalancedPrimitiveTree.node leaves h (2 * i)).polynomial
      (BalancedPrimitiveTree.node leaves h (2 * i + 1)).polynomial < 2 ^ BalancedMetadataTable.width f) :
    Consistent B (update B H (packet f (h + 1) i)) leaves (h + 1) i := by
  have hel : node B (child false (packet f (h + 1) i)) = (BalancedPrimitiveTree.node leaves h (2 * i)).polynomial := by
    rw [BalancedParameterContext.child_packet, node_packet]
    exact tree_eq_node B f leaves h (2 * i) hcl
  have her : node B (child true (packet f (h + 1) i)) = (BalancedPrimitiveTree.node leaves h (2 * i + 1)).polynomial := by
    rw [BalancedParameterContext.child_packet, node_packet]
    exact tree_eq_node B f leaves h (2 * i + 1) hcr
  have hl : leftDegree (packet f (h + 1) i) = (node B (child false (packet f (h + 1) i))).natDegree := by
    rw [leftDegree, hel, BalancedParameterContext.child_packet]
    exact hdl
  have hr : rightDegree (packet f (h + 1) i) = (node B (child true (packet f (h + 1) i))).natDegree := by
    rw [rightDegree, her, BalancedParameterContext.child_packet]
    exact hdr
  have hsl := (BalancedPrimitiveTree.node leaves h (2 * i)).separable_in_field (L := AlgebraicClosure ℚ)
  have hsr := (BalancedPrimitiveTree.node leaves h (2 * i + 1)).separable_in_field (L := AlgebraicClosure ℚ)
  rw [← hel] at hsl
  rw [← her] at hsr
  have hs := direction_eq_select B H (packet f (h + 1) i) hl hr hsl hsr hbl hbr
  rw [hel, her] at hs
  have hv : direction B H (packet f (h + 1) i) < 2 ^ BalancedMetadataTable.width f := by rw [hs]; exact hfit
  have hi' := child_index_lt n.size h i hh hi
  have hcell (which : Bool) (k l : ℕ) (hk : k ≤ n.size) (hl : l < 2 ^ (n.size - k)) :=
    (BalancedMetadataTable.cell_lt_capacity which n k l hk hl).trans_le hcap
  have hup : update B H (packet f (h + 1) i) =
      BalancedMetadataTable.replace f (2 * BalancedMetadataTable.key (h + 1) i + 1) (direction B H (packet f (h + 1) i)) := by
    simp only [update, BalancedParameterContext.original_packet, BalancedMetadataTable.cell,
      BalancedParameterContext.height_packet, BalancedParameterContext.index_packet, ite_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hup]
    exact consistent_replace_above B f leaves n (h + 1) i _ h (2 * i) hW hcap hv (by omega) (by omega) hi'.1 hcl
  · rw [hup]
    exact consistent_replace_above B f leaves n (h + 1) i _ h (2 * i + 1) hW hcap hv (by omega) (by omega) hi'.2 hcr
  · rw [update_order B H f (h + 1) i h (2 * i) hW
        (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell false h (2 * i) (by omega) hi'.1) hv]
    exact hdl
  · rw [update_order B H f (h + 1) i h (2 * i + 1) hW
        (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell false h (2 * i + 1) (by omega) hi'.2) hv]
    exact hdr
  · rw [update_direction B H f (h + 1) i hW (by simpa only [ite_true] using hcell true (h + 1) i hh hi) hv]
    exact hs

end Candidate
end LeanCanny.Algebra.BalancedTablePolynomials
