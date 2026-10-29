/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexAffineLevelEncoding
public import LeanCanny.Encoding.FlatAffineIntegerLiteral

/-! # Native ancestral level record decoding

The raw affine level record supplies the signed normal and constant. Earlier
stage references are clamped exactly as in the tower decoder. At depth zero
the selected output is always the constant, independently of the tag.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineLevelRecord
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open LeanCanny.Algebra
open scoped Classical

abbrev leftStage (k : ℕ) (r : List Bool) : ℕ := min (Nat.fromBitsLE (FlatAffineFullSourceTower.left r)) (k - 1)
abbrev rightStage (k : ℕ) (r : List Bool) : ℕ := min (Nat.fromBitsLE (FlatAffineFullSourceTower.right r)) (k - 1)

def fromRecord (base ancestor n W k : ℕ) (r : List Bool) : AffineLevel.Inputs where
  base := base
  count := n
  left := ancestor + leftStage k r * FlatAffineCriticalTower.width n
  right := ancestor + rightStage k r * FlatAffineCriticalTower.width n
  constant := FlatAffineFullSourceTower.integer W (FlatAffineFullSourceTower.constant r) 0
  normal i := FlatAffineFullSourceTower.integer W (FlatAffineFullSourceTower.normal r) i
  mode := if 0 < k then min (FlatAffineFullSourceTower.tag r) 4 else 0

private theorem flags_FP : FlatAffineFullSourceTower.flags ∈ FP := pairFst_mem_FP
private theorem left_FP : FlatAffineFullSourceTower.left ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
private theorem right_FP : FlatAffineFullSourceTower.right ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
private theorem normal_FP : FlatAffineFullSourceTower.normal ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairFst_mem_FP
private theorem constant_FP : FlatAffineFullSourceTower.constant ∈ FP :=
  mem_FP_comp (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP) pairSnd_mem_FP

theorem polyTime {base ancestor n W k : List Bool → ℕ} {record : List Bool → List Bool}
    (hb : UnaryFn base) (ha : UnaryFn ancestor) (hn : UnaryFn n) (hW : UnaryFn W) (hk : UnaryFn k) (hr : record ∈ FP) :
    AffineLevel.Inputs.PolyTime (fun c => fromRecord (base c) (ancestor c) (n c) (W c) (k c) (record c)) := by
  have hl := UnaryFn.fromBitsLE_min (mem_FP_comp hr left_FP) (hk.sub (UnaryFn.const 1))
  have hright := UnaryFn.fromBitsLE_min (mem_FP_comp hr right_FP) (hk.sub (UnaryFn.const 1))
  have hwidth := hn.add (hn.add (UnaryFn.const 1))
  have htagBits := take_mem_FP (drop_mem_FP (mem_FP_comp hr flags_FP) (UnaryFn.const 1)) (UnaryFn.const 2)
  have htag := UnaryFn.fromBitsLE_min htagBits (UnaryFn.const 4)
  refine ⟨hb, hn, ha.add (hl.mul hwidth), ha.add (hright.mul hwidth), ?_, ?_, ?_⟩
  · exact (UnaryFn.ite (FPPred.lt (UnaryFn.const 0) hk) htag (UnaryFn.const 0)).of_eq (fun _ => rfl)
  · have hc : (fun c => FlatAffineFullSourceTower.constant (record c)) ∈ FP :=
      mem_FP_comp (f := record) (g := FlatAffineFullSourceTower.constant) hr constant_FP
    exact FlatAffineIntegerLiteral.literal_FP (width := W) (index := fun _ => 0)
      (record := fun c => FlatAffineFullSourceTower.constant (record c)) hW (UnaryFn.const 0) hc
  · have hnormal : (fun c => FlatAffineFullSourceTower.normal (record c)) ∈ FP :=
      mem_FP_comp (f := record) (g := FlatAffineFullSourceTower.normal) hr normal_FP
    exact FlatAffineIntegerLiteral.literal_FP (width := W ∘ pairFst) (index := fun q => (pairSnd q).length)
      (record := fun q => FlatAffineFullSourceTower.normal (record (pairFst q)))
      (hW.comp pairFst_mem_FP) (UnaryFn.length pairSnd_mem_FP) (mem_FP_comp (f := pairFst) (g := fun c => FlatAffineFullSourceTower.normal (record c)) pairFst_mem_FP hnormal)

theorem valid (base ancestor n W k : ℕ) (r : List Bool)
    (hb : ancestor + (k + 1) * FlatAffineCriticalTower.width n ≤ base) :
    (fromRecord base ancestor n W k r).Valid := by
  have hl : leftStage k r ≤ k := (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hr : rightStage k r ≤ k := (Nat.min_le_right _ _).trans (Nat.sub_le _ _)
  have hnl : n ≤ FlatAffineCriticalTower.width n := by unfold FlatAffineCriticalTower.width; omega
  have hml := Nat.mul_le_mul_right (FlatAffineCriticalTower.width n) (show leftStage k r + 1 ≤ k + 1 by omega)
  have hmr := Nat.mul_le_mul_right (FlatAffineCriticalTower.width n) (show rightStage k r + 1 ≤ k + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at hml hmr
  exact ⟨by change ancestor + leftStage k r * FlatAffineCriticalTower.width n + n ≤ base; omega,
    by change ancestor + rightStage k r * FlatAffineCriticalTower.width n + n ≤ base; omega⟩

open scoped BigOperators in
theorem record_value (base ancestor n W k : ℕ) (r : List Bool) (x : ℕ → ℂ) :
    AffineLevel.value (fromRecord base ancestor n W k r) x =
      if 0 < k ∧ FlatAffineFullSourceTower.tag r = 1 then
        ∑ i ∈ Finset.range n, (FlatAffineFullSourceTower.integer W (FlatAffineFullSourceTower.normal r) i : ℂ) *
          x (ancestor + leftStage k r * FlatAffineCriticalTower.width n + i)
      else if 0 < k ∧ FlatAffineFullSourceTower.tag r = 2 then
        (∑ i ∈ Finset.range n, (FlatAffineFullSourceTower.integer W (FlatAffineFullSourceTower.normal r) i : ℂ) *
          x (ancestor + leftStage k r * FlatAffineCriticalTower.width n + i)) +
        ∑ i ∈ Finset.range n, (FlatAffineFullSourceTower.integer W (FlatAffineFullSourceTower.normal r) i : ℂ) *
          x (ancestor + rightStage k r * FlatAffineCriticalTower.width n + i)
      else (FlatAffineFullSourceTower.integer W (FlatAffineFullSourceTower.constant r) 0 : ℂ) := by
  have hm1 : min (FlatAffineFullSourceTower.tag r) 4 = 1 ↔ FlatAffineFullSourceTower.tag r = 1 := by omega
  have hm2 : min (FlatAffineFullSourceTower.tag r) 4 = 2 ↔ FlatAffineFullSourceTower.tag r = 2 := by omega
  unfold fromRecord AffineLevel.value
  by_cases hk : 0 < k
  · simp only [hk, ite_true, hm1, hm2, true_and]
  · norm_num only [hk, ite_false, false_and]

end LeanCanny.Encoding.FlatAffineLevelRecord
