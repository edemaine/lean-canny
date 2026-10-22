/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedDirectionPreparation
public import LeanCanny.Algebra.BalancedDirectionPreservation
public import LeanCanny.Algebra.PaddedAnnihilatorDirection

/-! # Preparing a consistent finite-annihilator metadata table

The invariant retains the original source, prepared width, capacity, and
exact degrees. An inner prefix preserves all children and completed parents;
the outer fold extends consistency one layer at a time.
-/

@[expose] public section

namespace LeanCanny.Algebra.PaddedAnnihilatorPreparation
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet)
open PaddedAnnihilatorBits
open BalancedDirectionPreparation

noncomputable def leaves (B : Family) (count : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (c : List Bool) : ℕ → SeparableIntegerPolynomial :=
  FiniteAnnihilatorTree.leaf (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (hne c)

structure Ready (B : Family) (count D : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0) (c f : List Bool) : Prop where
  source_eq : BalancedMetadataTable.source f = c
  width_eq : BalancedMetadataTable.width f = BalancedDegreeTable.width count D c
  capacity_le : BalancedMetadataTable.capacity (count c) ≤ BalancedMetadataTable.cells f
  orders : ∀ h i, h ≤ (count c).size → i < 2 ^ ((count c).size - h) →
    BalancedMetadataTable.order (packet f h i) = (BalancedPrimitiveTree.node (leaves B count hne c) h i).polynomial.natDegree

structure LayerState (B : Family) (count D : List Bool → ℕ)
    (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
    (c : List Bool) (h k : ℕ) (f : List Bool) : Prop where
  ready : Ready B count D hne c f
  lower : ∀ j, j < 2 ^ ((count c).size - h) → BalancedTablePolynomials.Consistent (family B count) f (leaves B count hne c) h j
  done : ∀ j, j < k → BalancedTablePolynomials.Consistent (family B count) f (leaves B count hne c) (h + 1) j

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)
variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)
variable (c : List Bool)

local notation "F" => family B count
local notation "H" => directionHeight count D b
local notation "L" => leaves B count hne c

include hdegree in
theorem ready_direction_fits (f : List Bool) (R : Ready B count D hne c f) (h i : ℕ)
    (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    BalancedTablePolynomials.Candidate.direction F H (packet f (h + 1) i) < 2 ^ BalancedMetadataTable.width f := by
  have hi' := BalancedTablePolynomials.child_index_lt (count c).size h i hh hi
  have hd : BalancedTablePolynomials.Candidate.degree (packet f (h + 1) i) =
      (BalancedPrimitiveTree.node L (h + 1) i).polynomial.natDegree := by
    simp only [BalancedTablePolynomials.Candidate.degree, BalancedTablePolynomials.Candidate.leftDegree,
      BalancedTablePolynomials.Candidate.rightDegree, BalancedParameterContext.child_packet,
      Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
    rw [R.orders h (2 * i) (by omega) hi'.1, R.orders h (2 * i + 1) (by omega) hi'.2,
      BalancedPrimitiveTree.node, SeparableIntegerPolynomial.combine_degree]
  have hb := BalancedDegreeTable.value_bound F count D (nonzero B count hne) (degree_bound B count D hdegree)
    c (2 * BalancedMetadataTable.key (h + 1) i)
  have he := BalancedDegreeTable.value_cell F count (nonzero B count hne) false c (h + 1) i hh
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at he
  rw [he, leaves_eq B count hne c] at hb
  have hd' : BalancedTablePolynomials.Candidate.degree (packet f (h + 1) i) ≤ BalancedDegreeTable.budget count D c := by
    rw [hd]; exact hb
  have hs := (BalancedTablePolynomials.Candidate.direction_le F H (packet f (h + 1) i)).trans (Nat.pow_le_pow_left hd' 2)
  have ht : (BalancedDegreeTable.budget count D c) ^ 2 < 2 ^ (2 * (BalancedDegreeTable.budget count D c).size) := by
    simpa only [← pow_mul, Nat.mul_comm] using Nat.pow_lt_pow_left (Nat.lt_size_self (BalancedDegreeTable.budget count D c)) (by decide : 2 ≠ 0)
  rw [R.width_eq]
  exact hs.trans_lt (ht.trans_le (Nat.pow_le_pow_right (by decide) (by unfold BalancedDegreeTable.width; omega)))

include hdegree in
theorem ready_update (f : List Bool) (R : Ready B count D hne c f) (h i : ℕ)
    (hh : h + 1 ≤ (count c).size) (hi : i < 2 ^ ((count c).size - (h + 1))) :
    Ready B count D hne c (BalancedTablePolynomials.Candidate.update F H (packet f (h + 1) i)) := by
  have hv := ready_direction_fits B count D b hne hdegree c f R h i hh hi
  have hW : 0 < BalancedMetadataTable.width f := by rw [R.width_eq]; exact BalancedDegreeTable.width_pos count D c
  obtain ⟨hs, hw, hc⟩ := update_fields F H f (h + 1) i
  refine ⟨hs.trans R.source_eq, hw.trans R.width_eq, ?_, ?_⟩
  · rw [hc]; exact R.capacity_le
  · intro k j hk hj
    have hcell := (BalancedMetadataTable.cell_lt_capacity false (count c) k j hk hj).trans_le R.capacity_le
    rw [BalancedTablePolynomials.Candidate.update_order F H f (h + 1) i k j hW
      (by simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using hcell) hv]
    exact R.orders k j hk hj

include hdegree hheight in
theorem layerRun_state (f : List Bool) (h k : ℕ) (R : Ready B count D hne c f)
    (hlower : ∀ j, j < 2 ^ ((count c).size - h) → BalancedTablePolynomials.Consistent F f L h j)
    (hh : h + 1 ≤ (count c).size) (hk : k ≤ 2 ^ ((count c).size - (h + 1))) :
    LayerState B count D hne c h k (layerRun F H f (h + 1) k) := by
  induction k with
  | zero => exact ⟨R, hlower, by intro j hj; omega⟩
  | succ k ih =>
    have S := ih (by omega)
    let t := layerRun F H f (h + 1) k
    have hk' : k < 2 ^ ((count c).size - (h + 1)) := by omega
    have hv := ready_direction_fits B count D b hne hdegree c t S.ready h k hh hk'
    have hW : 0 < BalancedMetadataTable.width t := by rw [S.ready.width_eq]; exact BalancedDegreeTable.width_pos count D c
    have hi' := BalancedTablePolynomials.child_index_lt (count c).size h k hh hk'
    refine ⟨ready_update B count D b hne hdegree c t S.ready h k hh hk', ?_, ?_⟩
    · intro j hj
      rw [layerRun, update_packet]
      exact BalancedTablePolynomials.consistent_replace_above F t L (count c) (h + 1) k _ h j hW S.ready.capacity_le hv
        (by omega) (by omega) hj (S.lower j hj)
    · intro j hj
      by_cases he : j = k
      · subst j
        exact updateDirection_consistent B count D b hne hdegree hheight t c h k S.ready.source_eq S.ready.width_eq
          S.ready.capacity_le hh hk' (S.lower (2 * k) hi'.1) (S.lower (2 * k + 1) hi'.2)
          (S.ready.orders h (2 * k) (by omega) hi'.1) (S.ready.orders h (2 * k + 1) (by omega) hi'.2)
      · rw [layerRun, update_packet]
        exact BalancedTablePolynomials.consistent_replace_peer F t L (count c) (h + 1) j k _ hW S.ready.capacity_le hv
          hh (by omega) he (S.done j (by omega))

include hdegree hheight in
theorem layer_ready_consistent (f : List Bool) (h : ℕ) (R : Ready B count D hne c f)
    (hlower : ∀ j, j < 2 ^ ((count c).size - h) → BalancedTablePolynomials.Consistent F f L h j)
    (hh : h + 1 ≤ (count c).size) :
    Ready B count D hne c (layer F H count (packet f (h + 1) 0)) ∧
      ∀ j, j < 2 ^ ((count c).size - (h + 1)) →
        BalancedTablePolynomials.Consistent F (layer F H count (packet f (h + 1) 0)) L (h + 1) j := by
  have he : layerCount count (packet f (h + 1) 0) = 2 ^ ((count c).size - (h + 1)) := by
    simp only [layerCount, BalancedParameterContext.original_packet, BalancedParameterContext.height_packet, R.source_eq]
  have S := layerRun_state B count D b hne hdegree hheight c f h (2 ^ ((count c).size - (h + 1))) R hlower hh le_rfl
  simpa only [layer, BalancedParameterContext.original_packet, BalancedParameterContext.height_packet, he] using ⟨S.ready, S.done⟩

include hdegree hheight in
theorem tableRun_ready_consistent (f : List Bool) (k : ℕ) (R : Ready B count D hne c f)
    (hzero : ∀ j, j < 2 ^ (count c).size → BalancedTablePolynomials.Consistent F f L 0 j)
    (hk : k ≤ (count c).size) :
    Ready B count D hne c (tableRun F H count f k) ∧
      ∀ j, j < 2 ^ ((count c).size - k) → BalancedTablePolynomials.Consistent F (tableRun F H count f k) L k j := by
  induction k with
  | zero => exact ⟨R, by simpa only [tableRun, Nat.sub_zero] using hzero⟩
  | succ k ih =>
    have S := ih (by omega)
    rw [tableRun, R.source_eq, min_eq_left (by omega : k ≤ (count c).size)]
    exact layer_ready_consistent B count D b hne hdegree hheight c (tableRun F H count f k) k S.1 S.2 hk

include hdegree in
theorem degrees_ready : Ready B count D hne c (prepareDegrees B count D c) := by
  refine ⟨BalancedDegreeTable.prepared_source F count D c, ?_, ?_, ?_⟩
  · exact BalancedMetadataTable.width_frame _ _ _ _
  · unfold prepareDegrees BalancedDegreeTable.prepare
    rw [BalancedMetadataTable.cells_frame _ _ _ _ (BalancedDegreeTable.width_pos count D c)]
  · exact prepared_order B count D hne hdegree c

noncomputable def prepare (B : Family) (count D b : List Bool → ℕ) (c : List Bool) : List Bool :=
  directions (family B count) (directionHeight count D b) count (prepareDegrees B count D c)

include hne hdegree in
theorem prepareEvaluator (A : Readers B) (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (prepare B count D b) :=
  (prepareDegreesEvaluator B A count D hn hD hne hdegree).chain
    (directionsEvaluator F (readers B A count hn) H count (directionHeight_binary hn hD hb) hn)

include hdegree hheight in
theorem prepare_consistent : BalancedTablePolynomials.Consistent F (prepare B count D b c) L (count c).size 0 := by
  have R := degrees_ready B count D hne hdegree c
  have S := tableRun_ready_consistent B count D b hne hdegree hheight c (prepareDegrees B count D c) (count c).size R
    (fun j _ => prepared_leaf_consistent B count D hne c j) le_rfl
  unfold prepare directions
  rw [R.source_eq]
  exact S.2 0 (by simp)

end LeanCanny.Algebra.PaddedAnnihilatorPreparation
