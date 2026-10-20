/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSign

/-! # Lowest deformation coefficients vanish at limits of deformed roots

Factor out the lowest deformation power before taking a limit. The remaining
polynomial is continuous in both the coefficient parameters and the deformation
value. A converging family of roots with nonzero deformation values therefore
annihilates the lowest coefficient at its limiting parameter.

This is the limit step in Canny's generalized characteristic polynomial argument.
It does not assert that such a root family exists for every isolated solution.
-/

@[expose] public section

namespace LeanCanny.Algebra.DeformationLowestCoefficient
open Polynomial Filter
open scoped Topology

theorem map_trailingCoeff_eq_zero_iff {R S : Type*} [Semiring R] [Semiring S]
    (p : Polynomial R) (φ : R →+* S) :
    φ p.trailingCoeff = 0 ↔ p.map φ = 0 ∨ p.natTrailingDegree < (p.map φ).natTrailingDegree := by
  by_cases hz : p.map φ = 0
  · have h := congrArg (fun q : Polynomial S => q.coeff p.natTrailingDegree) hz
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    simpa only [Polynomial.trailingCoeff, hz, true_or, iff_true] using h
  · have hle : p.natTrailingDegree ≤ (p.map φ).natTrailingDegree := by
      apply Polynomial.le_natTrailingDegree hz
      intro i hi
      rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, map_zero]
    rw [or_iff_right hz]
    constructor
    · intro h
      by_contra hn
      have he : (p.map φ).natTrailingDegree = p.natTrailingDegree := by omega
      have hc := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hz
      rw [he, Polynomial.coeff_map] at hc
      exact hc h
    · intro h
      have hc := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree h
      simpa only [Polynomial.coeff_map, Polynomial.trailingCoeff] using hc

theorem trailingCoeff_map_of_nonzero {R S : Type*} [Semiring R] [Semiring S]
    (p : Polynomial R) (φ : R →+* S) (h : φ p.trailingCoeff ≠ 0) :
    (p.map φ).natTrailingDegree = p.natTrailingDegree ∧ (p.map φ).trailingCoeff = φ p.trailingCoeff := by
  have hm : p.map φ ≠ 0 := by
    intro hz
    exact h ((map_trailingCoeff_eq_zero_iff p φ).mpr (Or.inl hz))
  have hle : p.natTrailingDegree ≤ (p.map φ).natTrailingDegree := by
    apply Polynomial.le_natTrailingDegree hm
    intro i hi
    rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi, map_zero]
  have hnot : ¬p.natTrailingDegree < (p.map φ).natTrailingDegree := by
    intro hl
    exact h ((map_trailingCoeff_eq_zero_iff p φ).mpr (Or.inr hl))
  have he : (p.map φ).natTrailingDegree = p.natTrailingDegree := by omega
  refine ⟨he, ?_⟩
  simp only [Polynomial.trailingCoeff, he, Polynomial.coeff_map]

variable {R K A I : Type*} [CommRing R] [Field K] [TopologicalSpace K]
  [IsTopologicalRing K] [T2Space K] [TopologicalSpace A]

omit [T2Space K] in
theorem continuous_eval₂ (p : Polynomial R) (φ : A → R →+* K)
    (hφ : ∀ r, Continuous (fun a => φ a r)) :
    Continuous (fun z : A × K => p.eval₂ (φ z.1) z.2) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    funext z
    exact Polynomial.eval₂_add _ _
  | monomial j r =>
    convert ((hφ r).comp continuous_fst).mul (continuous_snd.pow j) using 1
    funext z
    exact Polynomial.eval₂_monomial _ _

theorem trailingCoeff_eq_zero_of_tendsto (p : Polynomial R) (φ : A → R →+* K)
    (hφ : ∀ r, Continuous (fun a => φ a r)) (l : Filter I) [NeBot l]
    (a : I → A) (s : I → K) (a₀ : A)
    (ha : Tendsto a l (𝓝 a₀)) (hs : Tendsto s l (𝓝 0))
    (hne : ∀ᶠ i in l, s i ≠ 0)
    (hroot : ∀ᶠ i in l, p.eval₂ (φ (a i)) (s i) = 0) :
    φ a₀ p.trailingCoeff = 0 := by
  obtain ⟨q, hp, hq⟩ := InfinitesimalSign.factor_at_trailingDegree p
  have hzero : ∀ᶠ i in l, q.eval₂ (φ (a i)) (s i) = 0 := by
    filter_upwards [hne, hroot] with i hsi hpi
    rw [hp, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X] at hpi
    exact (mul_eq_zero.mp hpi).resolve_left (pow_ne_zero _ hsi)
  have ht : Tendsto (fun i => q.eval₂ (φ (a i)) (s i)) l
      (𝓝 (q.eval₂ (φ a₀) 0)) :=
    (continuous_eval₂ q φ hφ).continuousAt.tendsto.comp (ha.prodMk_nhds hs)
  have hz : Tendsto (fun i => q.eval₂ (φ (a i)) (s i)) l (𝓝 (0 : K)) :=
    tendsto_const_nhds.congr' (hzero.mono (fun _ h => h.symm))
  have he := tendsto_nhds_unique ht hz
  simpa only [Polynomial.eval₂_at_zero, hq] using he

end LeanCanny.Algebra.DeformationLowestCoefficient
