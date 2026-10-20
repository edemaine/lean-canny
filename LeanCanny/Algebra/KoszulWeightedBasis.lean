/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulMonomialBasis

/-! # Canonical bases of the finite weighted Koszul pieces

Sorting an injective exterior word changes it only by a unit sign; a
noninjective word vanishes. Thus the canonical monomial–subset family spans
the previously constructed weighted space and is a basis over any
commutative coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def monomialAlternating (k : ℕ) (m : Fin n →₀ ℕ) :
    (Fin n → Poly n R) [⋀^Fin k]→ₗ[Poly n R] Total n R :=
  ((Algebra.lsmul (Poly n R) (Poly n R) (Total n R)) (MvPolynomial.monomial m (1 : R))).compAlternatingMap
    (ExteriorAlgebra.ιMulti (Poly n R) k)

theorem monomialBlade_perm {k : ℕ} (v : Fin k → Fin n) (m : Fin n →₀ ℕ) (σ : Equiv.Perm (Fin k)) :
    monomialBlade (R := R) (v ∘ σ) m = (σ.sign : R) • monomialBlade (R := R) v m := by
  have h := (monomialAlternating (R := R) k m).map_perm
    (fun j => (Pi.single (v j) 1 : Fin n → Poly n R)) σ
  change monomialBlade (R := R) (v ∘ σ) m = σ.sign • monomialBlade (R := R) v m at h
  simpa only [Units.smul_def, Int.cast_smul_eq_zsmul] using h

theorem blade_eq_zero_of_not_injective {k : ℕ} (v : Fin k → Fin n) (hv : ¬Function.Injective v) :
    blade (R := R) v = 0 := by
  apply ExteriorAlgebra.ιMulti_eq_zero_of_not_inj
  intro h
  apply hv
  intro i j hij
  exact h (congrArg (fun t : Fin n => (Pi.single t 1 : Fin n → Poly n R)) hij)

theorem image_card_of_injective {k : ℕ} (v : Fin k → Fin n) (hv : Function.Injective v) :
    (Finset.univ.image v).card = k :=
  (Finset.card_image_of_injective Finset.univ hv).trans (Finset.card_fin k)

theorem subsetWeight_image {k : ℕ} (d : Fin n → ℕ) (v : Fin k → Fin n) (hv : Function.Injective v) :
    subsetWeight d (Finset.univ.image v) = wordWeight d v := by
  rw [subsetWeight, Finset.sum_image (by intro i _ j _ hij; exact hv hij)]
  rfl

noncomputable def sortPermutation {k : ℕ} (v : Fin k → Fin n) (hv : Function.Injective v) : Equiv.Perm (Fin k) :=
  (Finset.orderIsoOfFin (Finset.univ.image v) (image_card_of_injective v hv)).toEquiv.trans
    ((Set.equivOfEq Fintype.coe_image_univ).trans (Equiv.ofInjective v hv).symm)

theorem sortPermutation_order {k : ℕ} (v : Fin k → Fin n) (hv : Function.Injective v) :
    v ∘ sortPermutation v hv = (Finset.univ.image v).orderEmbOfFin (image_card_of_injective v hv) := by
  funext j
  let b : Set.range v := Set.equivOfEq Fintype.coe_image_univ
    ((Finset.univ.image v).orderIsoOfFin (image_card_of_injective v hv) j)
  change v ((Equiv.ofInjective v hv).symm b) = _
  exact Equiv.apply_ofInjective_symm hv b

theorem generator_mem_canonicalSpan (d : Fin n → ℕ) (L W k : ℕ) (a : Index d L W k) :
    generator (R := R) d L W k a ∈ canonicalSpan (R := R) d L W k := by
  by_cases hv : Function.Injective a.1
  · let s := Finset.univ.image a.1
    have hs : s.card = k := image_card_of_injective a.1 hv
    have hr : a.2.val ∈ canonicalIndices d L W k s := by
      rw [mem_canonicalIndices]
      refine ⟨hs, ?_⟩
      rw [subsetWeight_image d a.1 hv]
      exact (mem_indices d L W k a.1 a.2.val).mp a.2.property
    have hcan : canonicalGenerator (R := R) d L W k ⟨s, a.2.val, hr⟩ ∈ canonicalSpan (R := R) d L W k :=
      Submodule.subset_span (Set.mem_range_self _)
    rw [canonicalGenerator_apply, exteriorBasis_as_blade s hs] at hcan
    change monomialBlade (R := R) (s.orderEmbOfFin hs) (FixedWidthPolynomial.vector n W a.2.val) ∈ _ at hcan
    rw [← sortPermutation_order a.1 hv, monomialBlade_perm] at hcan
    have hu : IsUnit ((sortPermutation a.1 hv).sign : R) :=
      IsUnit.map (Int.castRingHom R) (sortPermutation a.1 hv).sign.isUnit
    exact (Submodule.smul_mem_iff_of_isUnit _ hu).mp hcan
  · change monomialBlade (R := R) a.1 (FixedWidthPolynomial.vector n W a.2.val) ∈ _
    rw [monomialBlade, blade_eq_zero_of_not_injective a.1 hv, smul_zero]
    exact Submodule.zero_mem _

theorem space_le_canonicalSpan (d : Fin n → ℕ) (L W k : ℕ) :
    space (R := R) d L W k ≤ canonicalSpan (R := R) d L W k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact generator_mem_canonicalSpan d L W k a

theorem canonicalSpan_eq_space (d : Fin n → ℕ) (L W k : ℕ) :
    canonicalSpan (R := R) d L W k = space (R := R) d L W k :=
  le_antisymm (canonicalSpan_le_space d L W k) (space_le_canonicalSpan d L W k)

noncomputable def canonicalBasis (d : Fin n → ℕ) (L W k : ℕ) :
    Module.Basis (CanonicalIndex d L W k) R (space (R := R) d L W k) :=
  (Module.Basis.span (canonicalGenerator_independent (R := R) d L W k)).map
    (LinearEquiv.ofEq _ _ (canonicalSpan_eq_space (R := R) d L W k))

theorem canonicalBasis_apply (d : Fin n → ℕ) (L W k : ℕ) (a : CanonicalIndex d L W k) :
    (canonicalBasis (R := R) d L W k a : Total n R) = canonicalGenerator (R := R) d L W k a := by
  change ((Module.Basis.span (canonicalGenerator_independent (R := R) d L W k)) a : Total n R) = _
  exact Module.Basis.coe_span_apply _ _

theorem canonicalBasis_repr (d : Fin n → ℕ) (L W k : ℕ) (x : space (R := R) d L W k)
    (a : CanonicalIndex d L W k) :
    (canonicalBasis (R := R) d L W k).repr x a =
      (ambientBasis (R := R)).repr x.val (canonicalEmbedding d L W k a) := by
  have h : (Finsupp.lapply a).comp (canonicalBasis (R := R) d L W k).repr.toLinearMap =
      (Finsupp.lapply (canonicalEmbedding d L W k a)).comp
        ((ambientBasis (R := R)).repr.toLinearMap.comp (space (R := R) d L W k).subtype) := by
    apply (canonicalBasis (R := R) d L W k).ext
    intro j
    change (canonicalBasis (R := R) d L W k).repr (canonicalBasis (R := R) d L W k j) a =
      (ambientBasis (R := R)).repr (canonicalBasis (R := R) d L W k j : Total n R)
        (canonicalEmbedding d L W k a)
    rw [canonicalBasis_apply]
    change _ = (ambientBasis (R := R)).repr
      (ambientBasis (R := R) (canonicalEmbedding d L W k j)) (canonicalEmbedding d L W k a)
    rw [Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
    simp only [(canonicalEmbedding_injective d L W k).eq_iff]
  exact LinearMap.congr_fun h x

theorem canonicalBasis_repr_coeff (d : Fin n → ℕ) (L W k : ℕ) (x : space (R := R) d L W k)
    (a : CanonicalIndex d L W k) :
    (canonicalBasis (R := R) d L W k).repr x a =
      ((exteriorBasis (R := R)).repr x.val a.1).coeff (FixedWidthPolynomial.vector n W a.2.val) := by
  rw [canonicalBasis_repr]
  exact ambientBasis_repr _ _ _

instance space_free (d : Fin n → ℕ) (L W k : ℕ) : Module.Free R (space (R := R) d L W k) :=
  Module.Free.of_basis (canonicalBasis (R := R) d L W k)

end LeanCanny.Algebra.KoszulWeighted
