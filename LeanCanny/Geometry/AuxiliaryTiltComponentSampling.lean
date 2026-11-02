/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.AuxiliaryTiltConstrainedSampling
public import LeanCanny.Geometry.UnboundedCoerciveComponents

/-! # Bounded auxiliary-tilted critical limits in each original clopen piece

The original zero set need not be compact. An isolating closed neighborhood is
lifted to a cylinder with a free auxiliary axis. Quartic comparison supplies a
fixed compact penalty sublevel, and each cluster point remains in the chosen
original piece. Criticality is obtained from local minimization, including at
singular original zeros.
-/
@[expose] public section
namespace LeanCanny.Geometry.AuxiliaryTiltComponentSampling
open AuxiliaryTiltEnergy AuxiliaryTiltConstrainedSampling CoercivePolynomialSampling CoerciveComponentSampling
open Set Filter MvPolynomial
open scoped Classical Topology
variable {n : ℕ}

theorem exists_critical_limits (q : MvPolynomial (Fin n) ℝ) (D : ℕ)
    (C : Set (Zeros q)) (hC : IsClopen C) (x0 : Zeros q) (hx0 : x0∈C)
    (δ : ℕ → ℝ) (hδ : ∀ k, 0<δ k) (hδ4 : ∀ k, δ k≤4) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ (y : ℕ → Fin (n+1) → ℝ) (a : Zeros q) (φ : ℕ → ℕ),
      a∈C ∧ StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 (Fin.snoc a.val 0)) ∧
      (∀ k, penalty D (y k)≤penalty D x0.val+1) ∧
      ∀ᶠ k in atTop, ∀ j, eval (y (φ k)) (pderiv j
        (TiltedCoerciveComponentSampling.polynomial (augmented q) D (Fin.last n) (δ (φ k))))=0 := by
  obtain ⟨S,hS,HA,HS,HI⟩ := UnboundedCoerciveComponents.isolating_neighborhood q C hC
  obtain ⟨y,a,φ,_,hm,hb,hφ,hl,ha,hq,hz⟩ := exists_minimizers_subsequence_on
    q D S hS x0.val (HA ⟨x0,hx0,rfl⟩) x0.property δ hδ hδ4 hδ0
  have HAC : restrict a∈Subtype.val '' C := HS _ hq ha
  have HC : (⟨restrict a,hq⟩ : Zeros q)∈C := by
    obtain ⟨z,hz,he⟩ := HAC
    have HZ : z=(⟨restrict a,hq⟩ : Zeros q) := Subtype.ext he
    exact HZ ▸ hz
  have Hsnoc : Fin.snoc (restrict a) 0=a := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hz.symm
    · simp only [Fin.snoc_castSucc,AuxiliaryTiltConstrainedSampling.restrict,Function.comp_def]
  refine ⟨y,⟨restrict a,hq⟩,φ,HC,hφ,?_,hb,?_⟩
  · rw [Hsnoc]
    exact hl
  · have HT := continuous_restrict.continuousAt.tendsto.comp hl
    filter_upwards [HT.eventually (isOpen_interior.mem_nhds (HI HAC))] with k hk
    have HN : cylinder S∈𝓝 (y (φ k)) := by
      exact mem_of_superset
        ((isOpen_interior.preimage continuous_restrict).mem_nhds hk) (by
          intro x hx
          change AuxiliaryTiltConstrainedSampling.restrict x∈S
          change AuxiliaryTiltConstrainedSampling.restrict x∈interior S at hx
          exact interior_subset hx)
    have HM : IsLocalMin (fun x => eval x
        (TiltedCoerciveComponentSampling.polynomial (augmented q) D (Fin.last n) (δ (φ k)))) (y (φ k)) := by
      simpa only [TiltedCoerciveComponentSampling.eval_polynomial] using (hm (φ k)).isLocalMin HN
    exact (LeanCanny.Geometry.PolynomialCalculus.critical_iff (RingHom.id ℝ) _ _).mp HM.fderiv_eq_zero

end LeanCanny.Geometry.AuxiliaryTiltComponentSampling
