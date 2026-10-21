/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedBasis
public import LeanCanny.Algebra.KoszulWeightedComplex
/-! # Projection onto a fixed total weight

In monomial exterior coordinates, retain only terms whose polynomial degree
plus input-degree weight equals the selected value. The projection is the
identity on that weighted space, commutes with the homogeneous Koszul
differential, and sends an exterior degree into its finite weighted piece.
-/

@[expose] public section

open scoped Classical BigOperators
namespace LeanCanny.Algebra.KoszulWeighted
variable {n : ℕ} {R : Type*} [CommRing R]
noncomputable def weightProjection (d : Fin n → ℕ) (L : ℕ) : Total n R →ₗ[R] Total n R :=
  (ambientBasis (R := R)).constr R (fun a =>
    if a.1.degree + subsetWeight d a.2 = L then ambientBasis a else 0)

theorem weightProjection_basis (d : Fin n → ℕ) (L : ℕ) (a : AmbientIndex n) :
    weightProjection (R := R) d L (ambientBasis a) =
      if a.1.degree + subsetWeight d a.2 = L then ambientBasis a else 0 :=
  Module.Basis.constr_basis _ _ _ _

theorem weightProjection_space (d : Fin n → ℕ) (L T W k : ℕ)
    (x : Total n R) (hx : x ∈ space (R := R) d T W k) :
    weightProjection d L x = if T = L then x else 0 := by
  have he : (weightProjection (R := R) d L).comp (space (R := R) d T W k).subtype =
      if T = L then (space (R := R) d T W k).subtype else 0 := by
    apply (canonicalBasis (R := R) d T W k).ext
    intro a
    have ha := (mem_canonicalIndices d T W k a.1 a.2.val).mp a.2.property
    by_cases hT : T = L
    · rw [ite_eq_left hT]
      change weightProjection d L ((canonicalBasis (R := R) d T W k a).val) =
        (canonicalBasis (R := R) d T W k a).val
      rw [canonicalBasis_apply]
      change weightProjection d L (ambientBasis (canonicalEmbedding d T W k a)) = _
      rw [weightProjection_basis]
      exact ite_eq_left (ha.2.trans hT)
    · rw [ite_eq_right hT]
      change weightProjection d L ((canonicalBasis (R := R) d T W k a).val) = 0
      rw [canonicalBasis_apply]
      change weightProjection d L (ambientBasis (canonicalEmbedding d T W k a)) = 0
      rw [weightProjection_basis]
      exact ite_eq_right (by change (FixedWidthPolynomial.vector n W a.2.val).degree + subsetWeight d a.1 ≠ L; rwa [ha.2])
  have hh := LinearMap.congr_fun he ⟨x, hx⟩
  by_cases hT : T = L
  · simpa only [ite_eq_left hT, LinearMap.comp_apply, Submodule.subtype_apply] using hh
  · simpa only [ite_eq_right hT, LinearMap.comp_apply, LinearMap.zero_apply, Submodule.subtype_apply] using hh

theorem weightProjection_differential (p : Fin n → Poly n R) (d : Fin n → ℕ) (L : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (x : Total n R) :
    weightProjection d L (KoszulExterior.differential p x) =
      KoszulExterior.differential p (weightProjection d L x) := by
  have he : (weightProjection (R := R) d L).comp ((KoszulExterior.differential p).restrictScalars R) =
      ((KoszulExterior.differential p).restrictScalars R).comp (weightProjection d L) := by
    apply (ambientBasis (R := R)).ext
    rintro ⟨m, s⟩
    let T := m.degree + subsetWeight d s
    have hx : ambientBasis (R := R) (m, s) ∈ space (R := R) d T T s.card := by
      rw [ambientBasis_apply, exteriorBasis_as_blade s rfl]
      exact monomialBlade_mem d T T s.card Nat.lt_two_pow_self _ m (by rw [wordWeight_ordered])
    change weightProjection d L (KoszulExterior.differential p (ambientBasis (m, s))) =
      KoszulExterior.differential p (weightProjection d L (ambientBasis (m, s)))
    rw [weightProjection_basis]
    change _ = KoszulExterior.differential p (if T = L then ambientBasis (m, s) else 0)
    cases hc : s.card with
    | zero =>
      rw [hc] at hx
      have hz := differential_degree_zero p d T T _ hx
      rw [hz, map_zero]
      split_ifs <;> simp only [hz, map_zero]
    | succ k =>
      rw [hc] at hx
      have hd := differential_mem p d T T k hp Nat.lt_two_pow_self _ hx
      rw [weightProjection_space d L T T k _ hd]
      split_ifs <;> simp only [map_zero]
  exact LinearMap.congr_fun he x

theorem weightProjection_smul_exteriorBasis_mem (d : Fin n → ℕ) (L W k : ℕ) (hW : L < 2 ^ W)
    (q : Poly n R) (s : Finset (Fin n)) (hs : s.card = k) :
    weightProjection d L (q • exteriorBasis (R := R) s) ∈ space (R := R) d L W k := by
  induction q using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [exteriorBasis_as_blade s hs, ← smul_monomialBlade, map_smul]
    have he : monomialBlade (R := R) (s.orderEmbOfFin hs) m = ambientBasis (m, s) := by
      rw [ambientBasis_apply, exteriorBasis_as_blade s hs]
      rfl
    rw [he, weightProjection_basis]
    by_cases hm : m.degree + subsetWeight d s = L
    · rw [ite_eq_left hm]
      apply Submodule.smul_mem
      rw [← he]
      exact monomialBlade_mem d L W k hW _ m (by rw [wordWeight_ordered]; exact hm)
    · rw [ite_eq_right hm, smul_zero]
      exact Submodule.zero_mem _
  | add q r hq hr =>
    rw [add_smul, map_add]
    exact Submodule.add_mem _ hq hr

theorem weightProjection_exteriorGrade_mem (d : Fin n → ℕ) (L W k : ℕ) (hW : L < 2 ^ W)
    (x : ExteriorAlgebra.exteriorPower (Poly n R) k (Fin n → Poly n R)) :
    weightProjection d L x.val ∈ space (R := R) d L W k := by
  let b := (Pi.basisFun (Poly n R) (Fin n)).exteriorPower k
  have he := congrArg Subtype.val (b.sum_repr x)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at he
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro s _
  change weightProjection d L ((b.repr x) s • (b s).val) ∈ _
  have hb : (b s).val = exteriorBasis (R := R) s.val :=
    (ExteriorAlgebra.basis_eq_coe_basis (Pi.basisFun (Poly n R) (Fin n)) s).symm
  rw [hb]
  exact weightProjection_smul_exteriorBasis_mem d L W k hW _ s.val s.property

end LeanCanny.Algebra.KoszulWeighted
