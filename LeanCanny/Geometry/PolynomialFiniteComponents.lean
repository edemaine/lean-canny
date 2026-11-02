/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.UnboundedCoerciveComponents
public import LeanCanny.Geometry.FiniteClopenWitness
/-! # Constructed finite component samples for every real polynomial zero set

No compactness, smoothness or connected-component oracle is an input. The
actual coercive eliminant's finite trailing grid meets every clopen piece;
this proves finite connected components and then samples each actual component.
These are connected covers: path/accessibility and effective native source
bounds are separate obligations.
-/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialFiniteComponents
open Set MvPolynomial CoerciveComponentSampling
open scoped Classical
variable {n : ℕ}

noncomputable def sample (q : MvPolynomial (Fin n) ℝ) (D : ℕ) : Set (Zeros q) :=
  Subtype.val ⁻¹' CoerciveComponentEliminants.grid q D

theorem finite_sample (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) : (sample q D).Finite :=
  (CoerciveComponentEliminants.finite_grid q D hD).preimage Subtype.val_injective.injOn

theorem components_finite (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) :
    Finite (ConnectedComponents (Zeros q)) := by
  apply FiniteClopenWitness.components_finite (sample q D) (finite_sample q D hD)
  intro C HC ⟨x,hx⟩
  obtain ⟨a,HA,HG⟩ := UnboundedCoerciveComponents.meets_piece q D hD C HC x hx
  exact ⟨a,HG,HA⟩

theorem component_sample (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) (x : Zeros q) :
    ∃ a : Zeros q, a∈connectedComponent x ∧ a∈sample q D := by
  let : Finite (ConnectedComponents (Zeros q)) := components_finite q D hD
  exact UnboundedCoerciveComponents.meets_piece q D hD (connectedComponent x)
    (FiniteComponentCover.isClopen_component x) x mem_connectedComponent

noncomputable def componentMap (q : MvPolynomial (Fin n) ℝ) (D : ℕ) : sample q D → ConnectedComponents (Zeros q) :=
  fun x => ConnectedComponents.mk x.val

theorem componentMap_surjective (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) :
    Function.Surjective (componentMap q D) := by
  intro c
  obtain ⟨x,HX⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨a,HA,HG⟩ := component_sample q D hD x
  exact ⟨⟨a,HG⟩,(ConnectedComponents.coe_eq_coe'.mpr HA).trans HX⟩

theorem card_le_sample (q : MvPolynomial (Fin n) ℝ) (D : ℕ) (hD : q.totalDegree≤D) :
    Nat.card (ConnectedComponents (Zeros q))≤Nat.card (sample q D) := by
  let : Finite (sample q D) := (finite_sample q D hD).to_subtype
  exact Nat.card_le_card_of_surjective _ (componentMap_surjective q D hD)
end LeanCanny.Geometry.PolynomialFiniteComponents
