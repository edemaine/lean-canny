/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Connected.Clopen

/-! # Finite connected components form a clopen cover -/

@[expose] public section
namespace LeanCanny.Geometry.FiniteComponentCover
open Set
open scoped Classical
variable {X : Type*} [TopologicalSpace X] [Finite (ConnectedComponents X)]

theorem isClopen_component (x : X) : IsClopen (connectedComponent x) := by
  let representative (c : ConnectedComponents X) : X := Classical.choose (ConnectedComponents.surjective_coe c)
  have HR (c : ConnectedComponents X) : ConnectedComponents.mk (representative c) = c :=
    Classical.choose_spec (ConnectedComponents.surjective_coe c)
  have HE : (connectedComponent x)ᶜ =
      ⋃ c : {c : ConnectedComponents X // c ≠ ConnectedComponents.mk x}, connectedComponent (representative c.val) := by
    ext y
    simp only [mem_compl_iff, mem_iUnion, Subtype.exists, exists_prop]
    constructor
    · intro hy
      refine ⟨ConnectedComponents.mk y, ?_, ?_⟩
      · intro H
        exact hy (ConnectedComponents.coe_eq_coe'.mp H)
      · exact ConnectedComponents.coe_eq_coe'.mp (HR (ConnectedComponents.mk y)).symm
    · rintro ⟨c, hc, hy⟩ hxy
      apply hc
      exact (HR c).symm.trans ((ConnectedComponents.coe_eq_coe'.mpr hy).symm.trans
        (ConnectedComponents.coe_eq_coe'.mpr hxy))
  refine ⟨isClosed_connectedComponent, ?_⟩
  rw [← isClosed_compl_iff, HE]
  exact isClosed_iUnion_of_finite (fun _ => isClosed_connectedComponent)

end LeanCanny.Geometry.FiniteComponentCover
