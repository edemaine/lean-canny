/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerReal
public import LeanCanny.Algebra.PositivePolynomialRoots
public import LeanCanny.Encoding.FlatAffinePowerSampleAccess

/-! # Native counts and existence for every original real affine critical root

The actual source degree is even. Its odd multiplier power bijects the real
power roots with the original roots, preserving every ambient coordinate.
Removing the unique dummy therefore transports complete native sampling to
the original Lagrange tower, including its singular roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerSampleInput
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

lemma multiplier_power_odd (F : Inputs) (u : List Bool) : Odd (FlatAffinePowerControls.degree F u - 1) := by
  change Odd (2 * (2 * BoundedZeroSource.degreeAllowance (BoundedFullWriter.size F.source u) + 1) - 1)
  exact ⟨2 * BoundedZeroSource.degreeAllowance (BoundedFullWriter.size F.source u), by omega⟩

abbrev OriginalRoots (F : Inputs) (u : List Bool) :=
  {z : Fin (FlatAffineFullSourceTower.count F u) → ℝ //
    ∀ i, (FlatAffineFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) z = 0}

noncomputable def originalRootsEquiv (F : Inputs) (u : List Bool) :
    {z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ //
      ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0} ≃ OriginalRoots F u := by
  have hD : 1 < FlatAffinePowerControls.degree F u := by
    have := FlatAffinePowerRowReaders.power_ne_zero F u
    unfold FlatAffinePowerRowReaders.power at this
    omega
  exact (PositivePolynomialSystem.rootsEquiv (Int.castRingHom ℝ) (FlatAffinePowerPositive.rawSystem F u)).trans
    (FlatAffinePowerTower.realRootEquiv (BoundedFullCriticalSamples.polynomial F.source u)
      (FlatAffinePowerControls.degree F u) hD (multiplier_power_odd F u)
      (FlatAffineFullSourceTower.free F u) (FlatAffineFullSourceTower.direction F u) (FlatAffineFullSourceTower.level F u))

lemma originalRootsEquiv_current (F : Inputs) (u : List Bool)
    (z : {z : Fin (FlatAffineFullSourcePositive.count F u) → ℝ //
      ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0})
    (t : Fin (F.depth u)) (i : Fin (FlatAffineFullSourceTower.arity F u)) :
    (originalRootsEquiv F u z).val (FlatAffinePowerTower.current t i) =
      z.val (FlatAffinePowerTower.current t i).castSucc := by
  change FlatAffinePowerTower.powerPoint (FlatAffinePowerControls.degree F u) (z.val ∘ Fin.castSucc)
    (FlatAffinePowerTower.current t i) = _
  rw [FlatAffinePowerTower.powerPoint_current]
  rfl

noncomputable def originalCount (F : Inputs) (u : List Bool) : ℕ := Nat.card (OriginalRoots F u)

lemma originalCount_depth_zero (F : Inputs) (u : List Bool) (hdepth : F.depth u = 0) : originalCount F u = 1 := by
  have hc : FlatAffineFullSourceTower.count F u = 0 := by
    unfold FlatAffineFullSourceTower.count
    rw [hdepth, zero_mul]
  let _ : Unique (OriginalRoots F u) := {
    default := ⟨fun _ => 0, fun i => by have := i.isLt; omega⟩
    uniq z := Subtype.ext (funext fun i => by have := i.isLt; omega) }
  exact Nat.card_unique

lemma originalCount_eq (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) (u : List Bool) :
    originalCount F u = SquareSampleComplete.count (input F hcone) u :=
  (Nat.card_congr (originalRootsEquiv F u)).symm

noncomputable def originalCountBound (F : Inputs) (u : List Bool) : ℕ :=
  FlatAffinePowerGram.degreeBound F u ^ FlatAffineFullSourcePositive.count F u

theorem originalCountBound_binary {F : Inputs} (h : F.Access) : BinaryFn (originalCountBound F) :=
  (FlatAffinePowerGram.degreeBound_binary h).powUnary (FlatAffineFullSourcePositive.count_unary h)

lemma originalCount_le (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) (u : List Bool) :
    originalCount F u ≤ originalCountBound F u := by
  rw [originalCount_eq F hcone]
  exact (SquareSampleComplete.finite_roots (input F hcone) (complete F hcone) u).2

theorem original_count_evaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    SpaceFunction (fun u => BinaryNatCode.encode (originalCount F u)) :=
  (count_evaluator h hcone).congr (funext fun u => congrArg BinaryNatCode.encode (originalCount_eq F hcone u).symm)

def originalLanguage (F : Inputs) : Language :=
  {u | ∃ z : Fin (FlatAffineFullSourceTower.count F u) → ℝ,
    ∀ i, (FlatAffineFullSourceTower.system F u i).eval₂ (Int.castRingHom ℝ) z = 0}

theorem originalLanguage_mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    originalLanguage F ∈ PSPACE := by
  have he : originalLanguage F = SquareSampleComplete.language (input F hcone) := by
    ext u
    constructor
    · rintro ⟨z, hz⟩
      let x := (originalRootsEquiv F u).symm ⟨z, hz⟩
      exact ⟨x.val, x.property⟩
    · rintro ⟨z, hz⟩
      let x := originalRootsEquiv F u ⟨z, hz⟩
      exact ⟨x.val, x.property⟩
  rw [he]
  exact SquareSampleComplete.language_mem_PSPACE (access h hcone) (complete F hcone)

end LeanCanny.Encoding.FlatAffinePowerSampleInput
