/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulMultidegree

/-! # A multidegree-dependent homotopy at the Macaulay level

Each multidegree of total degree `Macaulay.level d` admits an eligible
coordinate. Choosing its Macaulay pivot and using the polynomial coordinate
homotopy gives a coefficient-ring linear map. Preservation of multidegree
under the pure-power differential proves the homotopy identity on every
monomial exterior word at this level.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def levelHomotopy (d : Fin n → ℕ) : Total n R →ₗ[R] Total n R :=
  (ambientBasis (R := R)).constr R (fun a =>
    if h : (a.1 + subsetExponent d a.2).degree = Macaulay.level d then
      powerHomotopy (R := R) d (Macaulay.pivot d _ h) (ambientBasis (R := R) a)
    else 0)

theorem levelHomotopy_ambientBasis (d : Fin n → ℕ) (m : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    levelHomotopy (R := R) d (ambientBasis (R := R) (m, s)) =
      if h : (m + subsetExponent d s).degree = Macaulay.level d then
        powerHomotopy (R := R) d (Macaulay.pivot d _ h) (ambientBasis (R := R) (m, s))
      else 0 := Module.Basis.constr_basis _ _ _ _

theorem levelHomotopy_word (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ)
    (ht : (m + wordExponent d v).degree = Macaulay.level d) :
    levelHomotopy (R := R) d (monomialBlade (R := R) v m) =
      powerHomotopy (R := R) d (Macaulay.pivot d _ ht) (monomialBlade (R := R) v m) := by
  by_cases hv : Function.Injective v
  · have hs : (m + subsetExponent d (Finset.univ.image v)).degree = Macaulay.level d := by
      rw [wordExponent_image d v hv]
      exact ht
    have hh := levelHomotopy_ambientBasis (R := R) d m (Finset.univ.image v)
    rw [dite_eq_left hs] at hh
    simp only [wordExponent_image d v hv] at hh
    have hu : IsUnit ((sortPermutation v hv).sign : R) :=
      IsUnit.map (Int.castRingHom R) (sortPermutation v hv).sign.isUnit
    apply hu.smul_left_cancel.mp
    rw [← map_smul, ← monomialBlade_perm, monomialBlade_sorted, hh,
      ← monomialBlade_sorted v hv m, monomialBlade_perm, map_smul]
  · simp only [monomialBlade, blade_eq_zero_of_not_injective v hv, smul_zero, map_zero]

theorem levelHomotopy_component (d : Fin n → ℕ) (t : Fin n →₀ ℕ) (ht : t.degree = Macaulay.level d)
    (x : Total n R) (hx : x ∈ component (R := R) d t) :
    levelHomotopy (R := R) d x = powerHomotopy (R := R) d (Macaulay.pivot d t ht) x := by
  have hle : component (R := R) d t ≤ LinearMap.ker
      (levelHomotopy (R := R) d - powerHomotopy (R := R) d (Macaulay.pivot d t ht)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v, m, hm⟩, rfl⟩
    change levelHomotopy (R := R) d (monomialBlade (R := R) v m) -
      powerHomotopy (R := R) d (Macaulay.pivot d t ht) (monomialBlade (R := R) v m) = 0
    apply sub_eq_zero.mpr
    have hmt : (m + wordExponent d v).degree = Macaulay.level d := by rw [hm]; exact ht
    simpa only [hm] using levelHomotopy_word (R := R) d v m hmt
  exact sub_eq_zero.mp (hle hx)

theorem levelHomotopy_identity_word (d : Fin n → ℕ) {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ)
    (ht : (m + wordExponent d v).degree = Macaulay.level d) :
    KoszulExterior.differential (Macaulay.powers (R := R) d)
        (levelHomotopy (R := R) d (monomialBlade (R := R) v m)) +
      levelHomotopy (R := R) d
        (KoszulExterior.differential (Macaulay.powers (R := R) d) (monomialBlade (R := R) v m)) =
      monomialBlade (R := R) v m := by
  rw [levelHomotopy_word d v m ht,
    levelHomotopy_component d _ ht _ (powers_differential_word_mem_component d v m)]
  apply powerHomotopy_identity_word
  by_cases hi : Macaulay.pivot d (m + wordExponent d v) ht ∈ Set.range v
  · exact Or.inr hi
  · apply Or.inl
    apply Finsupp.single_le_iff.mpr
    have hp := Macaulay.pivot_le d (m + wordExponent d v) ht
    simpa only [Finsupp.add_apply, wordExponent_apply_of_not_mem d v _ hi, add_zero] using hp

end LeanCanny.Algebra.KoszulWeighted
