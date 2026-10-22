/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedDirectionScan
public import LeanCanny.Algebra.BalancedMetadataUpdate

/-! # Filling a direction cell by a native polynomial-space scan

The scan and fixed-width writer compose on every input. For a valid frame,
writing a fitting direction preserves its length and all degree cells.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials.Candidate
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet original)

noncomputable def update (B : Family) (H : List Bool → ℕ) (p : List Bool) : List Bool :=
  BalancedMetadataTable.replace (original p) (BalancedMetadataTable.cell true p) (direction B H p)

attribute [local irreducible] tree node BinaryNat.normalize BalancedMetadataTable.read

theorem updateEvaluator (B : Family) (A : Readers B) (H : List Bool → ℕ) (hH : BinaryFn H) :
    SpaceFunction (update B H) := by
  have hf := mem_FP_comp pairFst_mem_FP BalancedParameterContext.original_FP
  have hi : BinaryFn (BalancedMetadataTable.cell true ∘ pairFst) :=
    (BalancedMetadataTable.cell_binary true).comp pairFst_mem_FP
  have hv := BinaryFn.fromBits pairSnd_mem_FP
  have hw := BalancedMetadataTable.replace_mem_FP hf hi hv
  have E := (evaluator B A H hH).withInput.postcompose
    (fun s => BalancedMetadataTable.replace (original (pairFst s))
      (BalancedMetadataTable.cell true (pairFst s)) (Nat.fromBitsLE (pairSnd s))) hw
  exact E.congr (funext fun p => by
    simp only [update, Function.comp_apply, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem direction_le (B : Family) (H : List Bool → ℕ) (p : List Bool) :
    direction B H p ≤ degree p ^ 2 := by
  have hb := BoundedChoice.search_le (language B H) p (count p)
  dsimp only [direction, count] at *
  omega

theorem update_source (B : Family) (H : List Bool → ℕ) (p : List Bool) :
    BalancedMetadataTable.source (update B H p) = BalancedMetadataTable.source (original p) :=
  BalancedMetadataTable.source_replace _ _ _

theorem update_width (B : Family) (H : List Bool → ℕ) (p : List Bool) :
    BalancedMetadataTable.width (update B H p) = BalancedMetadataTable.width (original p) :=
  BalancedMetadataTable.width_replace _ _ _

theorem update_frame_length (B : Family) (H : List Bool → ℕ) (c : List Bool)
    (A W h i : ℕ) (values : ℕ → ℕ) (hW : 0 < W) :
    (update B H (packet (BalancedMetadataTable.frame c A W values) h i)).length =
      (BalancedMetadataTable.frame c A W values).length := by
  unfold update
  rw [BalancedParameterContext.original_packet]
  exact BalancedMetadataTable.replace_frame_length _ _ _ _ _ _ hW

theorem update_order (B : Family) (H : List Bool → ℕ) (f : List Bool) (h i k j : ℕ)
    (hW : 0 < BalancedMetadataTable.width f)
    (hk : 2 * BalancedMetadataTable.key k j < BalancedMetadataTable.cells f)
    (hv : direction B H (packet f h i) < 2 ^ BalancedMetadataTable.width f) :
    BalancedMetadataTable.order (packet (update B H (packet f h i)) k j) =
      BalancedMetadataTable.order (packet f k j) := by
  simp only [update, BalancedParameterContext.original_packet, BalancedMetadataTable.cell,
    BalancedParameterContext.height_packet, BalancedParameterContext.index_packet, ite_true]
  exact BalancedMetadataTable.order_replace_direction f (BalancedMetadataTable.key h i) _ k j hW hk hv

theorem update_direction (B : Family) (H : List Bool → ℕ) (f : List Bool) (h i : ℕ)
    (hW : 0 < BalancedMetadataTable.width f)
    (hk : 2 * BalancedMetadataTable.key h i + 1 < BalancedMetadataTable.cells f)
    (hv : direction B H (packet f h i) < 2 ^ BalancedMetadataTable.width f) :
    BalancedMetadataTable.direction (packet (update B H (packet f h i)) h i) = direction B H (packet f h i) := by
  simp only [update, BalancedParameterContext.original_packet, BalancedMetadataTable.cell,
    BalancedParameterContext.height_packet, BalancedParameterContext.index_packet, ite_true]
  exact BalancedMetadataTable.direction_replace_self f _ h i hW hk hv

end LeanCanny.Algebra.BalancedTablePolynomials.Candidate
