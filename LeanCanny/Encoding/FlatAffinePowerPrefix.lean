/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerPrefix
public import LeanCanny.Encoding.FlatAffineCompleteRootStages
public import LeanCanny.Encoding.SquareSampleProjectionChoice

/-! # Native ancestor labels for complete affine power roots

The coordinate map retains the earlier blocks and maps their extra zero
coordinate to the full tower's extra zero coordinate. Native bounded search
then computes a complete prefix label, without a Jacobian condition.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerPrefix
open LeanCanny.Algebra LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs)
open FlatAffineCompleteRootStages (truncate)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def projection (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (i : Fin (FlatAffineFullSourcePositive.count (truncate F d) u)) :
    Fin (FlatAffineFullSourcePositive.count F u) :=
  if hi : i.val < FlatAffineFullSourceTower.count (truncate F d) u then
    ⟨i.val, by
      have H := Nat.mul_le_mul_right (FlatAffineFullSourceTower.stageWidth F u) (hd u)
      change i.val < FlatAffineFullSourceTower.count F u + 1
      change d u * FlatAffineFullSourceTower.stageWidth F u ≤ FlatAffineFullSourceTower.count F u at H
      exact Nat.lt_succ_of_le (hi.le.trans H)⟩
  else Fin.last (FlatAffineFullSourceTower.count F u)

lemma projection_old (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (i : Fin (FlatAffineFullSourceTower.count (truncate F d) u)) :
    projection F d hd u i.castSucc = (FlatAffinePowerTower.prefixIndex (hd u) i).castSucc := by
  simp only [projection, Fin.val_castSucc, i.isLt, dite_true]
  rfl

lemma projection_last (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool) :
    projection F d hd u (Fin.last (FlatAffineFullSourceTower.count (truncate F d) u)) =
      Fin.last (FlatAffineFullSourceTower.count F u) := by
  simp only [projection, Fin.val_last, lt_self_iff_false, dite_false]

theorem roots_prefix {K : Type*} [CommRing K] (phi : ℤ →+* K)
    (F : Inputs) (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u : List Bool)
    (z : Fin (FlatAffineFullSourcePositive.count F u) → K)
    (hz : ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ phi z = 0) :
    ∀ i, (FlatAffinePowerPositive.system (truncate F d) u i).eval₂ phi (z ∘ projection F d hd u) = 0 := by
  have H := (PositivePolynomialSystem.roots_iff phi (FlatAffinePowerPositive.rawSystem F u) z).mp hz
  apply (PositivePolynomialSystem.roots_iff phi (FlatAffinePowerPositive.rawSystem (truncate F d) u) _).mpr
  constructor
  · have E := FlatAffinePowerTower.roots_prefix phi (hd u)
      (BoundedFullCriticalSamples.polynomial F.source u) (FlatAffinePowerControls.degree F u)
      (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u)
      (FlatAffineFullSourceTower.level F u) (z ∘ Fin.castSucc) H.1
    have HE : (z ∘ projection F d hd u) ∘ Fin.castSucc =
        (z ∘ Fin.castSucc) ∘ FlatAffinePowerTower.prefixIndex (hd u) := by
      funext i
      simp only [Function.comp_apply, projection_old]
    rw [HE]
    exact E
  · simpa only [Function.comp_apply, projection_last] using H.2

theorem coordinate_unary {F : Inputs} (h : F.Access) {d : List Bool → ℕ} (hdUnary : UnaryFn d)
    (hd : ∀ u, d u ≤ F.depth u) (cone : FlatAffinePowerPositive.ConeCertificate F) :
    UnaryFn (fun z => (SquareSampleProjectedThom.coordinate
      (FlatAffinePowerSampleInput.input F cone)
      (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
      (projection F d hd) (pairFst z) (pairSnd z)).val) := by
  have hdAccess := FlatAffineCompleteRootStages.access h hdUnary
  have hn := (FlatAffineFullSourceTower.count_unary hdAccess).comp pairFst_mem_FP
  have hi := UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hn
  have H := UnaryFn.ite (FPPred.lt hi hn) hi ((FlatAffineFullSourceTower.count_unary h).comp pairFst_mem_FP)
  apply H.of_eq
  intro z
  simp only [Function.comp_apply, SquareSampleProjectedThom.coordinate, SquareSampleInput.selected,
    FlatAffinePowerSampleInput.input, FlatAffineFullSourcePositive.count, Nat.add_sub_cancel,
    projection]
  split_ifs <;> rfl

noncomputable def value (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) : List Bool → List Bool :=
  SquareSampleProjectionChoice.value (FlatAffinePowerSampleInput.input F cone)
    (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
    (projection F d hd)

theorem evaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    {d : List Bool → ℕ} (hdUnary : UnaryFn d) (hd : ∀ u, d u ≤ F.depth u) :
    SpaceFunction (value F cone d hd) :=
  SquareSampleProjectionChoice.evaluator (FlatAffinePowerSampleInput.access h cone)
    (FlatAffinePowerSampleInput.access (FlatAffineCompleteRootStages.access h hdUnary)
      (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
    (projection F d hd) (coordinate_unary h hdUnary hd cone)

theorem value_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u w : List Bool)
    (hw : FlatAffineCompleteVertices.Valid F cone u w) :
    FlatAffineCompleteVertices.Valid (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd)
      u (value F cone d hd (pair u w)) :=
  SquareSampleProjectionChoice.value_valid (FlatAffinePowerSampleInput.input F cone)
    (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
    (FlatAffinePowerSampleInput.complete (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd)) (projection F d hd)
    (fun u x => roots_prefix (Int.castRingHom ℝ) F d hd u x.val x.property) u w hw

theorem value_point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (d : List Bool → ℕ) (hd : ∀ u, d u ≤ F.depth u) (u w : List Bool)
    (hw : FlatAffineCompleteVertices.Valid F cone u w) :
    (SquareSampleCompleteVertices.candidate
      (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
      u (value F cone d hd (pair u w)) (value_valid F cone d hd u w hw)).val =
    (SquareSampleCompleteVertices.candidate (FlatAffinePowerSampleInput.input F cone) u w hw).val ∘ projection F d hd u :=
  SquareSampleProjectionChoice.value_point (FlatAffinePowerSampleInput.input F cone)
    (FlatAffinePowerSampleInput.input (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd))
    (FlatAffinePowerSampleInput.complete (truncate F d) (FlatAffineCompleteRootStages.cone_prefix F cone d hd)) (projection F d hd)
    (fun u x => roots_prefix (Int.castRingHom ℝ) F d hd u x.val x.property) u w hw

end LeanCanny.Encoding.FlatAffinePowerPrefix
