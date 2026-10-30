/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineCompleteComponentSamples
public import LeanCanny.Geometry.FlatAffineSingularCriticalCharacterization

/-! # Complete native labels for every singular point of an affine slice

Independent slice normals give an original critical root with zero objective
multiplier at each singular point. The complete sampler retains those roots.
Under the next-stage cone certificate, the singular locus is finite and its
cardinality has the source-derived native critical-root bound.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSingularSliceSamples
open Set LeanCanny.Algebra LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteComponentSamples (source active direction levels ancestors slice)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def singular (F : Inputs) (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u) :
    Set (Fin (arity F u) → ℝ) :=
  {z | z ∈ slice F u x ∧ ¬Function.Surjective
    (FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ) (source F u) (active F u) (direction F u) z)}

theorem exists_label (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0)
    (z : Fin (arity F u) → ℝ) (hz : z ∈ singular F u x) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next F) cone u w},
      FlatAffineCompleteRootStages.project (next F) F.depth u (by change F.depth u ≤ F.depth u + 1; omega)
        (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w) = x ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val ∘ Sum.inl = z ∧
      newest F u (FlatAffineCompleteVertices.vertexEquiv (next F) cone u w).val (Sum.inr 0) = 0 := by
  obtain ⟨mu, hmu, hroot⟩ := FlatAffineSingularCriticalRoot.exists_stage_root_of_singular (Int.castRingHom ℝ)
    (source F u) (active F u) (direction F u) (levels F u) (ancestors F u x.val) z hz.1.1 hz.1.2 hheights hz.2
  let root := FlatAffineCompleteRootStages.extend F u x (Sum.elim z mu) hroot
  let w := (FlatAffineCompleteVertices.vertexEquiv (next F) cone u).symm root
  have HW : FlatAffineCompleteVertices.vertexEquiv (next F) cone u w = root := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [HW]
    exact FlatAffineCompleteRootStages.extend_prefix F u x (Sum.elim z mu) hroot
  · rw [HW, FlatAffineCompleteRootStages.extend_newest]
    rfl
  · rw [HW, FlatAffineCompleteRootStages.extend_newest]
    exact hmu

theorem finite_card_le (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate (next F))
    (u : List Bool) (x : FlatAffinePowerSampleInput.OriginalRoots F u)
    (hheights : ∀ c : active F u → ℝ, (∀ i, ∑ j : active F u, c j * (direction F u j.val.succ i : ℝ) = 0) → ∀ j, c j = 0) :
    Finite (singular F u x) ∧ Nat.card (singular F u x) ≤ FlatAffinePowerSampleInput.originalCountBound (next F) u := by
  let I := FlatAffinePowerSampleInput.input (next F) cone
  let : Finite (SquareSampleComplete.Roots I u) :=
    (SquareSampleComplete.finite_roots I (FlatAffinePowerSampleInput.complete (next F) cone) u).1
  let : Finite (FlatAffinePowerSampleInput.OriginalRoots (next F) u) :=
    Finite.of_equiv (SquareSampleComplete.Roots I u) (FlatAffinePowerSampleInput.originalRootsEquiv (next F) u)
  let f : singular F u x → FlatAffinePowerSampleInput.OriginalRoots (next F) u := fun z =>
    FlatAffineCompleteVertices.vertexEquiv (next F) cone u (Classical.choose (exists_label F cone u x hheights z.val z.property))
  have HF (z : singular F u x) : newest F u (f z).val ∘ Sum.inl = z.val :=
    (Classical.choose_spec (exists_label F cone u x hheights z.val z.property)).2.1
  have HI : Function.Injective f := by
    intro z v he
    apply Subtype.ext
    exact (HF z).symm.trans ((congrArg (fun r : FlatAffinePowerSampleInput.OriginalRoots (next F) u => newest F u r.val ∘ Sum.inl) he).trans (HF v))
  exact ⟨Finite.of_injective f HI, (Nat.card_le_card_of_injective f HI).trans
    (FlatAffinePowerSampleInput.originalCount_le (next F) cone u)⟩

end LeanCanny.Encoding.FlatAffineSingularSliceSamples
