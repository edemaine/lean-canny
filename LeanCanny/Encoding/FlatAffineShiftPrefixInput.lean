/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineFrozenPrefixCurves

/-! # Native frozen-prefix samplers computed from a varying-height row

The row's stage determines exactly how many earlier blocks remain unchanged.
This depth, the truncated source, and its complete sampler all have native
access from the original readers and row index. Ordinary height rows project
shifted roots to these frozen prefix roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineShiftPrefixInput
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs stageWidth)
open FlatAffineCompleteRootStages (truncate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def depth (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) : ℕ :=
  (row u).val / stageWidth F u

theorem depth_unary {F : Inputs} (h : F.Access)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (hr : UnaryFn (fun u => (row u).val)) :
    UnaryFn (depth F row) := hr.div (FlatAffineFullSourceTower.stageWidth_unary h)

lemma depth_le (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :
    depth F row u ≤ F.depth u := by
  have H : (row u).val ≤ F.depth u * stageWidth F u := by
    have H := (row u).isLt
    change (row u).val < F.depth u * stageWidth F u + 1 at H
    omega
  exact Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using H)

noncomputable def inputs (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) : Inputs :=
  truncate F (depth F row)

theorem access {F : Inputs} (h : F.Access)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (hr : UnaryFn (fun u => (row u).val)) :
    (inputs F row).Access := FlatAffineCompleteRootStages.access h (depth_unary h row hr)

theorem cone (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) : FlatAffinePowerPositive.ConeCertificate (inputs F row) :=
  FlatAffineCompleteRootStages.cone_prefix F C (depth F row) (depth_le F row)

noncomputable def input (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) : SquareSampleInput.Inputs :=
  FlatAffinePowerSampleInput.input (inputs F row) (cone F C row)

theorem inputAccess {F : Inputs} (h : F.Access) (C : FlatAffinePowerPositive.ConeCertificate F)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (hr : UnaryFn (fun u => (row u).val)) :
    (input F C row).Access := FlatAffinePowerSampleInput.access (access h row hr) (cone F C row)

lemma prefix_count_le_row (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :
    FlatAffineFullSourceTower.count (inputs F row) u ≤ (row u).val := Nat.div_mul_le_self _ _

theorem roots_prefix (F : Inputs) (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool)
    (hold : (row u).val < FlatAffineFullSourceTower.count F u) (t : ℝ)
    (z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ)
    (hz : ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = if i = row u then t else 0) :
    ∀ i, (FlatAffinePowerPositive.system (inputs F row) u i).eval₂ (Int.castRingHom ℝ)
      (z ∘ FlatAffinePowerPrefix.projection F (depth F row) (depth_le F row) u) = 0 :=
  FlatAffinePowerShiftPrefix.roots_prefix F (depth F row) (depth_le F row) u (row u) (prefix_count_le_row F row u) hold t z hz

theorem constant {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate F)
    (row : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool)
    (hold : (row u).val < FlatAffineFullSourceTower.count F u)
    (parameter : T → ℝ) (curve : T → Fin (FlatAffineFullSourcePositive.count F u) → ℝ)
    (hc : Continuous curve)
    (hroot : ∀ t i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) (curve t) = if i = row u then parameter t else 0)
    (s t : T) :
    curve s ∘ FlatAffinePowerPrefix.projection F (depth F row) (depth_le F row) u =
      curve t ∘ FlatAffinePowerPrefix.projection F (depth F row) (depth_le F row) u :=
  FlatAffineFrozenPrefixCurves.prefix_constant F C (depth F row) (depth_le F row) u (row u) (prefix_count_le_row F row u) hold parameter curve hc hroot s t

end LeanCanny.Encoding.FlatAffineShiftPrefixInput
