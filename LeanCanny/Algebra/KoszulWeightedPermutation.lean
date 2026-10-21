/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulCoordinatePermutation
public import LeanCanny.Algebra.KoszulWeightedContraction

/-! # Coordinate permutations on finite weighted Koszul pieces

Simultaneous spatial/exterior permutations preserve total weight when the
degree labels are permuted accordingly. Restricting the ambient equivalence
gives explicit equivalences of the finite weighted pieces, intertwining
the input differentials and the coordinate-power differentials.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem degree_equivMapDomain (ρ : Equiv.Perm (Fin n)) (m : Fin n →₀ ℕ) :
    (Finsupp.equivMapDomain ρ m).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.equivMapDomain_apply]
  exact Fintype.sum_equiv ρ.symm _ _ (fun _ => rfl)

theorem wordWeight_permutation (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ)
    (hdeg : ∀ i, e (ρ i) = d i) {k : ℕ} (v : Fin k → Fin n) : wordWeight e (ρ ∘ v) = wordWeight d v := by
  apply Finset.sum_congr rfl
  intro j _
  exact hdeg (v j)

theorem level_permutation (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ)
    (hdeg : ∀ i, e (ρ i) = d i) : Macaulay.level d = Macaulay.level e := by
  unfold Macaulay.level
  congr 1
  exact Fintype.sum_equiv ρ _ _ (fun i => congrArg (fun D => D - 1) (hdeg i).symm)

theorem coordinatePermutation_mem (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ) (hdeg : ∀ i, e (ρ i) = d i)
    (L M W Z k : ℕ) (hLM : L = M) (hZ : M < 2 ^ Z) (x : Total n R) (hx : x ∈ space (R := R) d L W k) :
    coordinatePermutation (R := R) ρ x ∈ space (R := R) e M Z k := by
  have hle : space (R := R) d L W k ≤ (space (R := R) e M Z k).comap (coordinatePermutation (R := R) ρ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change coordinatePermutation (R := R) ρ (monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val)) ∈ space (R := R) e M Z k
    rw [coordinatePermutation_monomialBlade]
    apply monomialBlade_mem e M Z k hZ
    rw [degree_equivMapDomain, wordWeight_permutation ρ d e hdeg]
    exact ((mem_indices d L W k a.1 a.2.val).mp a.2.property).trans hLM
  exact hle hx

noncomputable def coordinatePieceEquiv (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ) (hdeg : ∀ i, e (ρ i) = d i)
    (L M W Z k : ℕ) (hLM : L = M) (hW : L < 2 ^ W) (hZ : M < 2 ^ Z) :
    space (R := R) d L W k ≃ₗ[R] space (R := R) e M Z k := by
  let F : space (R := R) d L W k →ₗ[R] space (R := R) e M Z k :=
    ((coordinatePermutation (R := R) ρ).comp (space (R := R) d L W k).subtype).codRestrict _
      (fun x => coordinatePermutation_mem ρ d e hdeg L M W Z k hLM hZ x.val x.property)
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · intro x y he
    apply Subtype.ext
    have hi := congrArg (fun z : space (R := R) e M Z k => coordinatePermutation (R := R) ρ.symm z.val) he
    change coordinatePermutation ρ.symm (coordinatePermutation ρ x.val) =
      coordinatePermutation ρ.symm (coordinatePermutation ρ y.val) at hi
    simpa only [coordinatePermutation_left_inverse] using hi
  · intro x
    let y : space (R := R) d L W k := ⟨coordinatePermutation (R := R) ρ.symm x.val,
      coordinatePermutation_mem ρ.symm e d
        (fun i => by simpa only [Equiv.apply_symm_apply] using (hdeg (ρ.symm i)).symm)
        M L Z W k hLM.symm hW x.val x.property⟩
    refine ⟨y, Subtype.ext ?_⟩
    change coordinatePermutation (R := R) ρ (coordinatePermutation ρ.symm x.val) = x.val
    simpa only [Equiv.symm_symm] using coordinatePermutation_left_inverse (R := R) ρ.symm x.val

theorem coordinatePieceEquiv_apply (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ) (hdeg : ∀ i, e (ρ i) = d i)
    (L M W Z k : ℕ) (hLM : L = M) (hW : L < 2 ^ W) (hZ : M < 2 ^ Z) (x : space (R := R) d L W k) :
    (coordinatePieceEquiv (R := R) ρ d e hdeg L M W Z k hLM hW hZ x : Total n R) = coordinatePermutation ρ x.val := rfl

theorem coordinatePieceEquiv_chain (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ) (hdeg : ∀ i, e (ρ i) = d i)
    (L M W Z : ℕ) (hLM : L = M) (hW : L < 2 ^ W) (hZ : M < 2 ^ Z)
    (p q : Fin n → Poly n R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hq : ∀ i, (q i).IsHomogeneous (e i))
    (hinput : ∀ i, q (ρ i) = MvPolynomial.rename ρ (p i)) (k : ℕ) :
    (differential q e M Z hq hZ k).comp (coordinatePieceEquiv (R := R) ρ d e hdeg L M W Z (k + 1) hLM hW hZ).toLinearMap =
      (coordinatePieceEquiv (R := R) ρ d e hdeg L M W Z k hLM hW hZ).toLinearMap.comp (differential p d L W hp hW k) := by
  have he : permutedSystem ρ p = q := by
    funext i
    simpa only [permutedSystem, Equiv.apply_symm_apply] using (hinput (ρ.symm i)).symm
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change KoszulExterior.differential q (coordinatePermutation ρ x.val) = coordinatePermutation ρ (KoszulExterior.differential p x.val)
  rw [← he]
  exact (coordinatePermutation_differential ρ p x.val).symm

theorem coordinatePieceEquiv_power_chain (ρ : Equiv.Perm (Fin n)) (d e : Fin n → ℕ) (hdeg : ∀ i, e (ρ i) = d i)
    (L M W Z : ℕ) (hLM : L = M) (hW : L < 2 ^ W) (hZ : M < 2 ^ Z) (k : ℕ) :
    (differential (Macaulay.powers (R := R) e) e M Z (powers_homogeneous e) hZ k).comp
        (coordinatePieceEquiv (R := R) ρ d e hdeg L M W Z (k + 1) hLM hW hZ).toLinearMap =
      (coordinatePieceEquiv (R := R) ρ d e hdeg L M W Z k hLM hW hZ).toLinearMap.comp
        (differential (Macaulay.powers (R := R) d) d L W (powers_homogeneous d) hW k) := by
  apply coordinatePieceEquiv_chain ρ d e hdeg L M W Z hLM hW hZ _ _ (powers_homogeneous d) (powers_homogeneous e) _ k
  intro i
  simp only [Macaulay.powers, MvPolynomial.rename_monomial, Finsupp.mapDomain_single, hdeg]

end LeanCanny.Algebra.KoszulWeighted
