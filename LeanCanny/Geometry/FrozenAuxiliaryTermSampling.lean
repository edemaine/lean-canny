/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FrozenAuxiliaryComponentSampling
public import LeanCanny.Algebra.AuxiliaryTiltedTerm

/-! # Bounded frozen trajectories for the literal fixed-leading input term

One original degree bound D covers the auxiliary integer term. The source uses
Fermat degree 4D+2 and the tilt parameter s^(D+1); the two parameter powers are
identified explicitly. Original frozen coordinates and the clopen label survive.
-/
@[expose] public section
namespace LeanCanny.Geometry.FrozenAuxiliaryTermSampling
open LeanCanny.Algebra LeanCanny.ETR AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling
open Set Filter MvPolynomial
open scoped Classical Topology
variable {n : ℕ}

theorem exists_critical_limits (t : Term) (ha : t.arity≤n) (k : ℕ) (hk : k≤n) (a : Fin n → ℝ) (D : ℕ)
    (C : Set (slice (polynomial n t) k a)) (hC : IsClopen C)
    (x0 : slice (polynomial n t) k a) (hx0 : x0∈C)
    (s : ℕ → ℝ) (hs : ∀ i, 0<s i) (hs1 : ∀ i, s i≤1) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∃ (y : ℕ → Fin (n+1) → ℝ) (b : slice (polynomial n t) k a) (φ : ℕ → ℕ),
      b∈C ∧ StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 (Fin.snoc b.val 0)) ∧
      (∀ i j (hj : j.val<k), y i j=a ⟨j.val,by omega⟩) ∧
      ∀ᶠ i in atTop, ∀ j : Fin (n+1), k≤j.val →
        eval (y (φ i)) (pderiv j
          (FixedLeadingTiltedGradient.tilted k D (Fin.last n) (term n t) (s (φ i))))=0 := by
  have HP : ∀ i, (s i)^(D+1)≤4 := by
    intro i
    have H : (s i)^(D+1)≤1 := by simpa using pow_le_pow_left₀ (hs i).le (hs1 i) (D+1)
    linarith
  have HT : Tendsto (fun i => (s i)^(D+1)) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : D+1≠0)] using hs0.pow (D+1)
  obtain ⟨y,b,φ,hb,hφ,hl,hf,hc⟩ := FrozenAuxiliaryComponentSampling.exists_critical_limits
    (polynomial n t) k hk a (2*D) C hC x0 hx0 (fun i => (s i)^(D+1))
    (fun i => pow_pos (hs i) _) HP HT
  refine ⟨y,b,φ,hb,hφ,hl,hf,?_⟩
  filter_upwards [hc] with i hi
  intro j hj
  rw [AuxiliaryTiltedTerm.free_derivative_tilted k D (Fin.last n) j (term n t) (s (φ i)) hj,
    AuxiliaryTiltedTerm.polynomial_term n t ha]
  exact hi j hj

end LeanCanny.Geometry.FrozenAuxiliaryTermSampling
