/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedDirectionUpdate
public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Native bottom-up folds filling a balanced direction table

One fold scans each layer; another visits layers from the leaves upward.
Both retain only the fixed-size metadata frame. Their space certificates
hold on arbitrary words and need no consistency or source-bound promises.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedDirectionPreparation
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (packet original height)
open BalancedMetadataTable (source width cells)

theorem update_packet (B : Family) (H : List Bool → ℕ) (f : List Bool) (h i : ℕ) :
    BalancedTablePolynomials.Candidate.update B H (packet f h i) =
      BalancedMetadataTable.replace f (2 * BalancedMetadataTable.key h i + 1)
        (BalancedTablePolynomials.Candidate.direction B H (packet f h i)) := by
  simp only [BalancedTablePolynomials.Candidate.update, BalancedParameterContext.original_packet,
    BalancedMetadataTable.cell, BalancedParameterContext.height_packet, BalancedParameterContext.index_packet, ite_true]

theorem update_fields (B : Family) (H : List Bool → ℕ) (f : List Bool) (h i : ℕ) :
    source (BalancedTablePolynomials.Candidate.update B H (packet f h i)) = source f ∧
    width (BalancedTablePolynomials.Candidate.update B H (packet f h i)) = width f ∧
    cells (BalancedTablePolynomials.Candidate.update B H (packet f h i)) = cells f := by
  simp only [update_packet, BalancedMetadataTable.source_replace, BalancedMetadataTable.width_replace,
    BalancedMetadataTable.cells_replace, and_self]

noncomputable def layerRun (B : Family) (H : List Bool → ℕ) (f : List Bool) (h : ℕ) : ℕ → List Bool
  | 0 => f
  | k + 1 => BalancedTablePolynomials.Candidate.update B H (packet (layerRun B H f h k) h k)

theorem layerRun_fields (B : Family) (H : List Bool → ℕ) (f : List Bool) (h k : ℕ) :
    source (layerRun B H f h k) = source f ∧ width (layerRun B H f h k) = width f ∧
      cells (layerRun B H f h k) = cells f := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨hs, hw, hc⟩ := update_fields B H (layerRun B H f h k) h k
    exact ⟨hs.trans ih.1, hw.trans ih.2.1, hc.trans ih.2.2⟩

theorem layerRun_length_succ (B : Family) (H : List Bool → ℕ) (f : List Bool) (h k : ℕ) :
    (layerRun B H f h (k + 1)).length = 2 * (source f).length + 2 * width f + cells f * width f + 4 := by
  rw [layerRun, update_packet, BalancedMetadataTable.replace_length]
  obtain ⟨hs, hw, hc⟩ := layerRun_fields B H f h k
  rw [hs, hw, hc]

theorem layerRun_length_le (B : Family) (H : List Bool → ℕ) (f : List Bool) (h k : ℕ) :
    (layerRun B H f h k).length ≤ 5 * f.length + 4 := by
  cases k with
  | zero => dsimp only [layerRun]; omega
  | succ k =>
    rw [layerRun_length_succ]
    simpa only [BalancedMetadataTable.replace_length] using BalancedMetadataTable.replace_length_le f 0 0

def layerCount (count : List Bool → ℕ) (p : List Bool) : ℕ :=
  2 ^ ((count (source (original p))).size - height p)

theorem layerCount_binary {count : List Bool → ℕ} (hn : UnaryFn count) : BinaryFn (layerCount count) := by
  have hc := mem_FP_comp BalancedParameterContext.original_FP BalancedMetadataTable.source_FP
  have hs : UnaryFn (fun p => (count (source (original p))).size) := (hn.comp hc).size
  exact (BinaryFn.const 2).powUnary (hs.sub BalancedParameterContext.height_unary)

noncomputable def layer (B : Family) (H count : List Bool → ℕ) (p : List Bool) : List Bool :=
  layerRun B H (original p) (height p) (layerCount count p)

def layerQuery (q : List Bool) : List Bool :=
  packet (BoundedFold.accumulator q) (height (pairFst q)) (Nat.fromBitsLE (BoundedFold.counter q))

theorem layerQuery_FP : layerQuery ∈ FP :=
  BalancedParameterContext.packet_FP BoundedFold.accumulator_mem_FP
    (BalancedParameterContext.height_unary.comp pairFst_mem_FP) (BinaryFn.fromBits BoundedFold.counter_mem_FP)

noncomputable def layerStep (B : Family) (H : List Bool → ℕ) : List Bool → List Bool :=
  BalancedTablePolynomials.Candidate.update B H ∘ layerQuery

theorem layer_fold (B : Family) (H : List Bool → ℕ) (p : List Bool) (k : ℕ) :
    BoundedFold.fold (layerStep B H) original p k = layerRun B H (original p) (height p) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih, layerRun]
    simp only [layerStep, Function.comp_apply, layerQuery, BoundedFold.accumulator_packet,
      BoundedFold.context_packet, BoundedFold.counter_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem layerEvaluator (B : Family) (A : Readers B) (H count : List Bool → ℕ)
    (hH : BinaryFn H) (hn : UnaryFn count) : SpaceFunction (layer B H count) := by
  have E : SpaceFunction (layerStep B H) :=
    (BalancedTablePolynomials.Candidate.updateEvaluator B A H hH).precompose layerQuery layerQuery_FP
  have R := BoundedFold.evaluator E (fun p => BinaryNatCode.encode (layerCount count p)) original
    (layerCount_binary hn).bits_mem_FP BalancedParameterContext.original_FP
    (Polynomial.C 5 * Polynomial.X + Polynomial.C 4) (fun p k _ => by
      rw [layer_fold]
      have hb := layerRun_length_le B H (original p) (height p) k
      have hp : (original p).length ≤ p.length := pairFst_length_le p
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      change (layerRun B H (original p) (height p) k).length ≤ 5 * p.length + 4
      omega)
  exact R.congr (funext fun p => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rw [layer_fold]; rfl)

noncomputable def tableRun (B : Family) (H count : List Bool → ℕ) (f : List Bool) : ℕ → List Bool
  | 0 => f
  | k + 1 => layer B H count (packet (tableRun B H count f k) (min k (count (source f)).size + 1) 0)

theorem tableRun_fields (B : Family) (H count : List Bool → ℕ) (f : List Bool) (k : ℕ) :
    source (tableRun B H count f k) = source f ∧ width (tableRun B H count f k) = width f ∧
      cells (tableRun B H count f k) = cells f := by
  induction k with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    simp only [tableRun, layer, BalancedParameterContext.original_packet, BalancedParameterContext.height_packet]
    obtain ⟨hs, hw, hc⟩ := layerRun_fields B H (tableRun B H count f k)
      (min k (count (source f)).size + 1) (layerCount count (packet (tableRun B H count f k) (min k (count (source f)).size + 1) 0))
    exact ⟨hs.trans ih.1, hw.trans ih.2.1, hc.trans ih.2.2⟩

theorem tableRun_length_succ (B : Family) (H count : List Bool → ℕ) (f : List Bool) (k : ℕ) :
    (tableRun B H count f (k + 1)).length = 2 * (source f).length + 2 * width f + cells f * width f + 4 := by
  simp only [tableRun, layer, layerCount, BalancedParameterContext.original_packet, BalancedParameterContext.height_packet]
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (Nat.two_pow_pos
    ((count (source (tableRun B H count f k))).size - (min k (count (source f)).size + 1))))
  rw [hj, layerRun_length_succ]
  obtain ⟨hs, hw, hc⟩ := tableRun_fields B H count f k
  rw [hs, hw, hc]

theorem tableRun_length_le (B : Family) (H count : List Bool → ℕ) (f : List Bool) (k : ℕ) :
    (tableRun B H count f k).length ≤ 5 * f.length + 4 := by
  cases k with
  | zero => dsimp only [tableRun]; omega
  | succ k =>
    rw [tableRun_length_succ]
    simpa only [BalancedMetadataTable.replace_length] using BalancedMetadataTable.replace_length_le f 0 0

noncomputable def directions (B : Family) (H count : List Bool → ℕ) (f : List Bool) : List Bool :=
  tableRun B H count f (count (source f)).size

def tableQuery (count : List Bool → ℕ) (q : List Bool) : List Bool :=
  packet (BoundedFold.accumulator q) (min (Nat.fromBitsLE (BoundedFold.counter q)) (count (source (pairFst q))).size + 1) 0

theorem tableQuery_FP {count : List Bool → ℕ} (hn : UnaryFn count) : tableQuery count ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP BalancedMetadataTable.source_FP
  have hs : UnaryFn (fun p => (count (source (pairFst p))).size) := (hn.comp hc).size
  exact BalancedParameterContext.packet_FP BoundedFold.accumulator_mem_FP
    ((UnaryFn.fromBitsLE_min BoundedFold.counter_mem_FP hs).add (UnaryFn.const 1)) (BinaryFn.const 0)

noncomputable def tableStep (B : Family) (H count : List Bool → ℕ) : List Bool → List Bool :=
  layer B H count ∘ tableQuery count

theorem table_fold (B : Family) (H count : List Bool → ℕ) (f : List Bool) (k : ℕ) :
    BoundedFold.fold (tableStep B H count) id f k = tableRun B H count f k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [BoundedFold.fold, ih, tableRun]
    simp only [tableStep, Function.comp_apply, tableQuery, BoundedFold.accumulator_packet,
      BoundedFold.context_packet, BoundedFold.counter_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem directionsEvaluator (B : Family) (A : Readers B) (H count : List Bool → ℕ)
    (hH : BinaryFn H) (hn : UnaryFn count) : SpaceFunction (directions B H count) := by
  have E : SpaceFunction (tableStep B H count) :=
    (layerEvaluator B A H count hH hn).precompose (tableQuery count) (tableQuery_FP hn)
  have hs : UnaryFn (fun f => (count (source f)).size) := (hn.comp BalancedMetadataTable.source_FP).size
  have R := BoundedFold.evaluator E (fun f => BinaryNatCode.encode (count (source f)).size) id
    (bits_mem_FP hs) id_mem_FP (Polynomial.C 5 * Polynomial.X + Polynomial.C 4) (fun f k _ => by
      rw [table_fold]
      simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
        using tableRun_length_le B H count f k)
  exact R.congr (funext fun f => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]; rw [table_fold]; rfl)

end LeanCanny.Algebra.BalancedDirectionPreparation
