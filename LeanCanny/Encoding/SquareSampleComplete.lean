/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleEquationCount

/-! # Native sampling counts for all captured square-system roots

When the coordinate annihilators retain every root, equation tests alone
select a complete finite sampler. The existing primitive coordinates and
native equation counter therefore count all roots, including singular ones.
Completeness is a mathematical property of the supplied annihilators; it
adds no runtime reader or count oracle to the native input interface.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleComplete
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCoordinates (parameter coordinate)
open SquareSampleParameters (decode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] parameter coordinate

/-- The stronger annihilation property supplied by a no-infinity certificate. -/
def Complete (F : Inputs) : Prop :=
  ∀ u (z : Fin (F.count u) → ℝ),
    (∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0) →
    ∀ i, (F.annihilator u i).eval₂ (Int.castRingHom ℝ) (z i) = 0

abbrev Roots (F : Inputs) (u : List Bool) :=
  {z : Fin (F.count u) → ℝ // ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0}

theorem root_complete (F : Inputs) (hF : Complete F) (u : List Bool)
    (z : Fin (F.count u) → ℝ) (hz : ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0) :
    ∃ theta : ℝ, (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧ decode F u theta = z := by
  obtain ⟨theta, ht, hx⟩ := SquareSampleCoordinates.tuple_complete F u z (fun i => by
    rw [SquareSampleSource.polynomial_packet]
    exact hF u z hz i)
  exact ⟨theta, ht, funext fun i => (hx i).2⟩

noncomputable def candidate (F : Inputs) (u : List Bool) (theta : SquareSampleFilters.Roots F u) : Roots F u :=
  ⟨decode F u theta.val, theta.property.2⟩

theorem candidate_injective (F : Inputs) (u : List Bool) : Function.Injective (candidate F u) := by
  intro theta theta' he
  apply Subtype.ext
  apply SquareSampleCoordinates.parameter_roots_ext F u theta.val theta'.val theta.property.1 theta'.property.1
  intro i
  exact congrFun (congrArg (fun z : Roots F u => z.val) he) i

theorem candidate_surjective (F : Inputs) (hF : Complete F) (u : List Bool) :
    Function.Surjective (candidate F u) := by
  intro z
  obtain ⟨theta, ht, he⟩ := root_complete F hF u z.val z.property
  have hz : ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0 := by
    rw [he]
    exact z.property
  exact ⟨⟨theta, ht, hz⟩, Subtype.ext he⟩

noncomputable def rootEquiv (F : Inputs) (hF : Complete F) (u : List Bool) :
    SquareSampleFilters.Roots F u ≃ Roots F u :=
  Equiv.ofBijective (candidate F u) ⟨candidate_injective F u, candidate_surjective F hF u⟩

theorem finite_roots (F : Inputs) (hF : Complete F) (u : List Bool) :
    Finite (Roots F u) ∧ Nat.card (Roots F u) ≤ F.annDegree u ^ F.count u := by
  have H := RootBranchCount.finite_card_le (fun z : Roots F u => z.val) Subtype.val_injective
    (fun i => (F.annihilator u i).map (Int.castRingHom ℝ))
    (fun i => (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (F.ann_nonzero u i))
    (fun z i => by rw [Polynomial.eval_map]; exact hF u z.val z.property i)
  refine ⟨H.1, H.2.trans ?_⟩
  calc
    _ ≤ ∏ _i : Fin (F.count u), F.annDegree u := Finset.prod_le_prod fun i _ =>
      Polynomial.natDegree_map_le.trans (F.ann_degree u i)
    _ = _ := by simp

noncomputable def count (F : Inputs) (u : List Bool) : ℕ := Nat.card (Roots F u)

theorem count_eq_equation_count (F : Inputs) (hF : Complete F) (u : List Bool) :
    count F u = SquareSampleEquationCount.count F u :=
  (Nat.card_congr (rootEquiv F hF u)).symm

theorem count_evaluator {F : Inputs} (h : F.Access) (hF : Complete F) :
    SpaceFunction (fun u => BinaryNatCode.encode (count F u)) :=
  (SquareSampleEquationCount.evaluator h).congr (funext fun u =>
    congrArg BinaryNatCode.encode (count_eq_equation_count F hF u).symm)

def language (F : Inputs) : Language := {u | ∃ z : Fin (F.count u) → ℝ,
  ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0}

theorem language_eq (F : Inputs) (hF : Complete F) : language F = SquareSampleEquationCount.language F := by
  ext u
  change (∃ z, ∀ i, (F.system u i).eval₂ (Int.castRingHom ℝ) z = 0) ↔ Nonempty (SquareSampleFilters.Roots F u)
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨(rootEquiv F hF u).symm ⟨z, hz⟩⟩
  · rintro ⟨theta⟩
    exact ⟨(candidate F u theta).val, (candidate F u theta).property⟩

theorem language_mem_PSPACE {F : Inputs} (h : F.Access) (hF : Complete F) : language F ∈ PSPACE := by
  rw [language_eq F hF]
  exact SquareSampleEquationCount.language_mem_PSPACE h

end LeanCanny.Encoding.SquareSampleComplete
