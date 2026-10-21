/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalPermutation
public import LeanCanny.Algebra.MacaulayUniversalTransport

/-! # Universal numerator/denominator comparisons across all orderings

The concrete simultaneous input/spatial permutation intertwines both
finite differentials. The proved determinant transport therefore gives
the polynomial cross-comparison for every pair of universal orderings.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

theorem numerator_denominator_cross (d : Fin n → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W)
    (π σ : Equiv.Perm (Fin n)) (hπ : Macaulay.level (d ∘ π) < 2 ^ W) (hσ : Macaulay.level (d ∘ σ) < 2 ^ W) :
    numerator (R := R) d W π * denominator d W σ = numerator d W σ * denominator d W π := by
  let ρ := π.trans σ.symm
  have hr (i : Fin n) : σ (ρ i) = π i := σ.apply_symm_apply (π i)
  have hd (i : Fin n) : (d ∘ σ) (ρ i) = (d ∘ π) i := congrArg d (hr i)
  have hlevel := KoszulWeighted.level_permutation ρ (d ∘ π) (d ∘ σ) hd
  let T := fun k => KoszulWeighted.coordinatePieceEquiv (R := FractionRing (CoefficientRing n R))
    ρ (d ∘ π) (d ∘ σ) hd (Macaulay.level (d ∘ π)) (Macaulay.level (d ∘ σ)) W W k hlevel hπ hσ
  apply cross_of_transport (R := R) d W hdegree π σ hπ hσ T
  · intro k
    exact KoszulWeighted.coordinatePieceEquiv_power_chain ρ (d ∘ π) (d ∘ σ) hd
      (Macaulay.level (d ∘ π)) (Macaulay.level (d ∘ σ)) W W hlevel hπ hσ k
  · intro k
    exact KoszulWeighted.coordinatePieceEquiv_chain ρ (d ∘ π) (d ∘ σ) hd
      (Macaulay.level (d ∘ π)) (Macaulay.level (d ∘ σ)) W W hlevel hπ hσ
      (fractionSystem (R := R) d W π) (fractionSystem (R := R) d W σ)
      (fractionSystem_homogeneous (R := R) d W π) (fractionSystem_homogeneous (R := R) d W σ)
      (fun i => (fractionSystem_rename d W π σ ρ hr i).symm) k

theorem level_comp_perm (d : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : Macaulay.level (d ∘ π) = Macaulay.level d :=
  KoszulWeighted.level_permutation π (d ∘ π) d (fun _ => rfl)

theorem ordering_cross (d : Fin n → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W)
    (hW : Macaulay.level d < 2 ^ W) (π σ : Equiv.Perm (Fin n)) :
    numerator (R := R) d W π * denominator d W σ = numerator d W σ * denominator d W π :=
  numerator_denominator_cross d W hdegree π σ (by rwa [level_comp_perm]) (by rwa [level_comp_perm])

end LeanCanny.Algebra.MacaulayUniversal
