/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FiniteClopenWitness
/-! # Finite connected-component covers pass through a finite continuous image cover -/
@[expose] public section
namespace LeanCanny.Geometry.FiniteComponentImages
open Set
open scoped Classical
variable {I : Type*} [Finite I] {X : I → Type*} [∀ i, TopologicalSpace (X i)]
  [∀ i, Finite (ConnectedComponents (X i))] {Y : Type*} [TopologicalSpace Y]

theorem components_finite (f : (i : I) → X i → Y) (hf : ∀ i, Continuous (f i))
    (cover : ∀ y, ∃ i x, f i x=y) : Finite (ConnectedComponents Y) := by
  let representative (i : I) (c : ConnectedComponents (X i)) := Classical.choose (ConnectedComponents.surjective_coe c)
  have HR (i : I) (c : ConnectedComponents (X i)) : ConnectedComponents.mk (representative i c)=c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  let F : ((i : I) × ConnectedComponents (X i)) → Y := fun z => f z.1 (representative z.1 z.2)
  apply FiniteClopenWitness.components_finite (Set.range F) (Set.finite_range F)
  intro C HC ⟨y,HY⟩
  obtain ⟨i,x,HX⟩ := cover y
  have HH : connectedComponent x ⊆ f i ⁻¹' C :=
    isPreconnected_connectedComponent.subset_isClopen (HC.preimage (hf i)) ⟨x,mem_connectedComponent,by change f i x∈C; rw [HX]; exact HY⟩
  have HA : representative i (ConnectedComponents.mk x)∈connectedComponent x := ConnectedComponents.coe_eq_coe'.mp (HR i _)
  exact ⟨F ⟨i,ConnectedComponents.mk x⟩,⟨⟨i,ConnectedComponents.mk x⟩,rfl⟩,HH HA⟩
end LeanCanny.Geometry.FiniteComponentImages
