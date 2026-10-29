/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PositivePolynomialInfinity
public import LeanCanny.Algebra.FlatAffinePowerConeBridge
public import LeanCanny.Encoding.FlatAffinePowerGramBounds

/-! # Original cone certificates give nonzero complete coordinate annihilators

The actual writer source splits into its lower-degree part and pure-power
leading form. Stage cone exclusion applies to the whole ancestry tower and
survives the forced-zero completion, including depth zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerPositive
open LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

noncomputable def lower (F : Inputs) (u : List Bool) : MvPolynomial (Fin (arity F u)) ℤ :=
  rename (BoundedFullGeometry.inputIndex (F.source.dim u + 3))
    (IntegerRegularSource.lower (BoundedRegularSource.lower (BoundedFullWriter.original F.source u)
      (BoundedFullWriter.size F.source u) (BoundedFullWriter.size F.source u) (F.source.radius u))
      (FlatAffinePowerControls.degree F u)
      (BoundedRegularSource.sourceMassExponent (F.source.dim u) (BoundedFullWriter.size F.source u)
        (BoundedFullWriter.size F.source u) (F.source.radius u)))

noncomputable def leading (F : Inputs) (u : List Bool) : MvPolynomial (Fin (arity F u)) ℤ :=
  C (IntegerRegularSource.leading (F.source.dim u + 3) 1 (FlatAffinePowerControls.degree F u)
    (BoundedRegularSource.sourceMassExponent (F.source.dim u) (BoundedFullWriter.size F.source u)
      (BoundedFullWriter.size F.source u) (F.source.radius u))) *
    ∑ i : Fin (arity F u), X i ^ FlatAffinePowerControls.degree F u

lemma source_eq (F : Inputs) (u : List Bool) :
    BoundedFullCriticalSamples.polynomial F.source u = lower F u + leading F u := by
  unfold BoundedFullCriticalSamples.polynomial
  rw [BoundedFullGeometry.polynomial_eq]
  rfl

lemma lower_degree (F : Inputs) (u : List Bool) : (lower F u).totalDegree < FlatAffinePowerControls.degree F u :=
  (totalDegree_rename_le _ _).trans_lt (IntegerRegularSource.lower_degree _ _ _
    (BoundedRegularSource.lower_degree _ _ _ _ (BoundedFullWriter.original_degree F.source u)))

lemma leading_homogeneous (F : Inputs) (u : List Bool) :
    (leading F u).IsHomogeneous (FlatAffinePowerControls.degree F u) := by
  apply IsHomogeneous.C_mul
  apply IsHomogeneous.sum
  intro i _
  simpa only [one_mul] using (isHomogeneous_X (R := ℤ) i).pow (FlatAffinePowerControls.degree F u)

def ConeCertificate (F : Inputs) : Prop :=
  ∀ u (t : Fin (F.depth u)), FlatAffinePowerTower.ConeRootFree (leading F u)
    (FlatAffineFullSourceTower.free F u t.val) (FlatAffineFullSourceTower.direction F u t.val)

/-- The original rational/complex cone exclusion certificate suffices. -/
theorem coneCertificate_of_critical (F : Inputs)
    (h : ∀ u (t : Fin (F.depth u)), AffineConeDirectionGeometry.CriticalRootFree (K := ℚ) (L := ℂ)
      ((leading F u).map (Int.castRingHom ℚ)) (FlatAffineFullSourceTower.free F u t.val)
      (fun r i => (FlatAffineFullSourceTower.direction F u t.val r.succ i : ℚ))
      (fun i => (FlatAffineFullSourceTower.direction F u t.val 0 i : ℂ))) : ConeCertificate F := by
  intro u t
  exact FlatAffinePowerTower.coneRootFree_of_critical _ _ _ (h u t)

lemma raw_noInfinity (F : Inputs) (h : ConeCertificate F) (u : List Bool) :
    AffineFiniteCoordinates.NoInfinity (rawSystem F u)
      (FlatAffinePowerTower.degrees (n := arity F u) (k := F.depth u) (FlatAffinePowerControls.degree F u)) := by
  have hD : 1 < FlatAffinePowerControls.degree F u := by
    have := FlatAffinePowerRowReaders.power_ne_zero F u
    unfold FlatAffinePowerRowReaders.power at this
    omega
  unfold rawSystem
  rw [source_eq]
  exact FlatAffinePowerTower.noInfinity (lower F u) (leading F u) _ (lower_degree F u)
    (leading_homogeneous F u) hD _ _ _ (h u)

theorem noInfinity (F : Inputs) (h : ConeCertificate F) (u : List Bool) :
    AffineFiniteCoordinates.NoInfinity (system F u) (degree F u) :=
  PositivePolynomialSystem.noInfinity (rawSystem F u) _ (raw_noInfinity F h u)

theorem annihilator_ne_zero (F : Inputs) (h : ConeCertificate F)
    (coordinate : (u : List Bool) → Fin (FlatAffineFullSourcePositive.count F u)) (u : List Bool) :
    FlatAffinePowerGram.annihilator F coordinate u ≠ 0 := by
  rw [FlatAffinePowerGram.annihilator_eq]
  exact AffineFiniteCoordinates.ne_zero _ _ (degree_pos F u) (noInfinity F h u) (coordinate u)

end LeanCanny.Encoding.FlatAffinePowerPositive
