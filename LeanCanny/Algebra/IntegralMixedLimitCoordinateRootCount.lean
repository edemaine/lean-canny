/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRoot
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRealization
public import Mathlib.Data.Set.Card
/-! # Selected limit-coordinate roots have the original scalar-width bound

Valid choices all select the same nonzero polynomial after the old real hom.
Their union therefore has at most the relative degree many distinct roots,
without multiplying by the number of formal trailing-coefficient choices.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinate
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def roots (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : Set ℝ :=
  {v | ∃ c : Fin (ChoiceBound P r), Valid x hm r j φ c ∧ ((factor x hm r j c).map φ.toRingHom).eval v=0}

theorem roots_eq_of_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c) :
    roots x hm r j φ = {v | ((factor x hm r j c).map φ.toRingHom).eval v=0} := by
  ext v
  constructor
  · rintro ⟨d,hd,hv⟩
    have HE := (selected_factor_eq x hm r j φ d hd).trans (selected_factor_eq x hm r j φ c hc).symm
    simpa only [HE,Set.mem_ofPred_eq] using hv
  · intro hv
    exact ⟨c,hc,hv⟩

theorem roots_finite (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (roots x hm r j φ).Finite := by
  obtain ⟨c,hc⟩ := exists_valid x hm r j φ
  rw [roots_eq_of_valid x hm r j φ c hc]
  simpa only [IsRoot] using finite_setOfPred_isRoot hc.2

theorem roots_ncard_le_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (roots x hm r j φ).ncard ≤ degree P r := by
  obtain ⟨c,hc⟩ := exists_valid x hm r j φ
  let p := (factor x hm r j c).map φ.toRingHom
  have HS : roots x hm r j φ ⊆ (p.roots.toFinset : Set ℝ) := by
    rw [roots_eq_of_valid x hm r j φ c hc]
    intro v hv
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hc.2).mpr hv)
  calc
    (roots x hm r j φ).ncard ≤ (p.roots.toFinset : Set ℝ).ncard := Set.ncard_le_ncard HS (Finset.finite_toSet _)
    _ = p.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ degree P r := selected_degree_bound x hm r j φ c

theorem roots_ncard_le_width (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (roots x hm r j φ).ncard ≤ 2^B :=
  (roots_ncard_le_degree x hm r j φ).trans (degree_cap x r)

end LeanCanny.Algebra.IntegralMixedLimitCoordinate
