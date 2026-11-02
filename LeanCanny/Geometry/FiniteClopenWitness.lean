/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FiniteComponentCover
public import Mathlib.Data.Fintype.Card
/-! # A finite set meeting every nonempty clopen set forces finitely many components -/
@[expose] public section
namespace LeanCanny.Geometry.FiniteClopenWitness
open Set
open scoped Classical
variable {X : Type*} [TopologicalSpace X]

theorem components_finite (K : Set X) (hK : K.Finite)
    (hit : ∀ C : Set X, IsClopen C → C.Nonempty → ∃ x∈K, x∈C) :
    Finite (ConnectedComponents X) := by
  by_contra H
  let : Infinite (ConnectedComponents X) := not_finite_iff_infinite.mp H
  let : Finite K := hK.to_subtype
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨U,HC,HN,HD,_HU⟩ := ConnectedComponents.exists_fun_isClopen_of_infinite X
    (Fintype.card K+1) (Nat.succ_pos _)
  choose x hxK hxU using fun i => hit (U i) (HC i) (HN i)
  let f : Fin (Fintype.card K+1) → K := fun i => ⟨x i,hxK i⟩
  have HF : Function.Injective f := by
    intro i j HJ
    by_contra HN
    have HE : x i=x j := congrArg Subtype.val HJ
    exact (Set.disjoint_left.mp (HD HN)) (hxU i) (HE ▸ hxU j)
  have HB := Fintype.card_le_of_injective f HF
  simp only [Fintype.card_fin] at HB
  omega
end LeanCanny.Geometry.FiniteClopenWitness
