/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenAuxiliaryTiltTransport

/-! # Bounded critical trajectories in a correlated frozen original slice

The first k original coordinates remain literally equal to the chosen real
parameters. Clopen labels are pulled back along this actual substitution; no
absolute elimination root or unrelated hom is introduced. The auxiliary last
axis stays free and supplies the bounded tilt.
-/
@[expose] public section
namespace LeanCanny.Geometry.FrozenAuxiliaryComponentSampling
open MvPolynomial FrozenCoordinateSubstitution CoerciveComponentSampling CoercivePolynomialSampling
open AuxiliaryTiltEnergy
open Set Filter
open scoped Classical Topology
variable {n : ℕ}

noncomputable def slice (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | q.eval x=0 ∧ ∀ i, i.val<k → x i=a i}

noncomputable def project (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (a : Fin n → ℝ) :
    Zeros (substitute k a q) → slice q k a := fun z =>
  ⟨point k a z.val,by
    constructor
    · have H : (substitute k a q).eval z.val=0 := z.property
      rw [eval_substitute] at H
      exact H
    · intro i hi
      simp only [point,hi,ite_true]⟩

theorem continuous_project (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (a : Fin n → ℝ) :
    Continuous (project q k a) :=
  ((continuous_point k a).comp continuous_subtype_val).subtype_mk _

theorem exists_critical_limits (q : MvPolynomial (Fin n) ℝ) (k : ℕ) (hk : k≤n) (a : Fin n → ℝ) (D : ℕ)
    (C : Set (slice q k a)) (hC : IsClopen C) (x0 : slice q k a) (hx0 : x0∈C)
    (δ : ℕ → ℝ) (hδ : ∀ i, 0<δ i) (hδ4 : ∀ i, δ i≤4) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ (y : ℕ → Fin (n+1) → ℝ) (b : slice q k a) (φ : ℕ → ℕ),
      b∈C ∧ StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 (Fin.snoc b.val 0)) ∧
      (∀ i j (hj : j.val<k), y i j=a ⟨j.val,by omega⟩) ∧
      ∀ᶠ i in atTop, ∀ j : Fin (n+1), k≤j.val →
        eval (y (φ i)) (pderiv j
          (TiltedCoerciveComponentSampling.polynomial (augmented q) D (Fin.last n) (δ (φ i))))=0 := by
  have HX : point k a x0.val=x0.val := point_fixed k a x0.val x0.property.2
  let x0' : Zeros (substitute k a q) := ⟨x0.val,by change (substitute k a q).eval x0.val=0; rw [eval_substitute,HX]; exact x0.property.1⟩
  have HP : project q k a x0'=x0 := Subtype.ext HX
  obtain ⟨y,b,φ,hb,hφ,hl,_,hc⟩ := AuxiliaryTiltComponentSampling.exists_critical_limits
    (substitute k a q) D ((project q k a) ⁻¹' C) (hC.preimage (continuous_project q k a)) x0'
    (by change project q k a x0'∈C; rw [HP]; exact hx0) δ hδ hδ4 hδ0
  let z : ℕ → Fin (n+1) → ℝ := fun i => point k (Fin.snoc a 0) (y i)
  have HL : Tendsto (z ∘ φ) atTop (𝓝 (Fin.snoc (project q k a b).val 0)) := by
    have H := (continuous_point k (Fin.snoc a 0)).continuousAt.tendsto.comp hl
    rw [point_snoc k hk a b.val 0 0] at H
    exact H
  refine ⟨z,project q k a b,φ,hb,hφ,HL,?_,?_⟩
  · intro i j
    refine Fin.lastCases ?_ (fun h => ?_) j
    · intro hj
      have H : n<k := hj
      omega
    · intro hj
      change h.val<k at hj
      simp only [z,point,Fin.val_castSucc,hj,ite_true,Fin.snoc_castSucc]
  · filter_upwards [hc] with i hi
    intro j hj
    change eval (point k (Fin.snoc a 0) (y (φ i))) _=0
    rw [eval_augmented_tilt_free k hk a q D (δ (φ i)) (y (φ i)) j hj]
    exact hi j

end LeanCanny.Geometry.FrozenAuxiliaryComponentSampling
