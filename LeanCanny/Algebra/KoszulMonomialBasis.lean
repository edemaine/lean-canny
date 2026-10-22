/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedSpace
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Canonical monomial and exterior coordinates

The polynomial monomial basis and the ordered exterior basis give a basis
of the full exterior algebra over the original coefficient ring. Selecting
the subset cardinality and total weight gives a finite independent family
for each weighted piece.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def exteriorBasis : Module.Basis (Finset (Fin n)) (Poly n R) (Total n R) :=
  (Pi.basisFun (Poly n R) (Fin n)).ExteriorAlgebra

abbrev AmbientIndex (n : ℕ) := (Fin n →₀ ℕ) × Finset (Fin n)

noncomputable def ambientBasis : Module.Basis (AmbientIndex n) R (Total n R) :=
  (MvPolynomial.basisMonomials (Fin n) R).smulTower exteriorBasis

theorem ambientBasis_apply (m : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    ambientBasis (R := R) (m, s) = MvPolynomial.monomial m (1 : R) • exteriorBasis (R := R) s := by
  rw [ambientBasis, Module.Basis.smulTower_apply]
  rfl

theorem ambientBasis_repr (x : Total n R) (m : Fin n →₀ ℕ) (s : Finset (Fin n)) :
    (ambientBasis (R := R)).repr x (m, s) = ((exteriorBasis (R := R)).repr x s).coeff m := by
  rw [ambientBasis, Module.Basis.smulTower_repr_mk]
  rfl

def subsetWeight (d : Fin n → ℕ) (s : Finset (Fin n)) : ℕ := ∑ i ∈ s, d i

theorem wordWeight_ordered (d : Fin n → ℕ) (s : Finset (Fin n)) {k : ℕ} (hs : s.card = k) :
    wordWeight d (s.orderEmbOfFin hs) = subsetWeight d s := by
  calc
    _ = ∑ i : s, d i.val :=
      Fintype.sum_equiv (s.orderIsoOfFin hs).toEquiv _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort _ _

theorem exteriorBasis_as_blade (s : Finset (Fin n)) {k : ℕ} (hs : s.card = k) :
    exteriorBasis (R := R) s = blade (R := R) (s.orderEmbOfFin hs) := by
  rw [exteriorBasis, ExteriorAlgebra.basis_apply_ofCard _ hs]
  change ExteriorAlgebra.ιMulti (Poly n R) k ((Pi.basisFun (Poly n R) (Fin n)) ∘ s.orderEmbOfFin hs) = _
  unfold blade
  congr 1
  funext j
  simp only [Function.comp_apply, Pi.basisFun_apply]

noncomputable def canonicalIndices (d : Fin n → ℕ) (L W k : ℕ) (s : Finset (Fin n)) : Finset (Macaulay.Index n W) :=
  Finset.univ.filter (fun r => s.card = k ∧ (FixedWidthPolynomial.vector n W r).degree + subsetWeight d s = L)

theorem mem_canonicalIndices (d : Fin n → ℕ) (L W k : ℕ) (s : Finset (Fin n)) (r : Macaulay.Index n W) :
    r ∈ canonicalIndices d L W k s ↔ s.card = k ∧ (FixedWidthPolynomial.vector n W r).degree + subsetWeight d s = L := by
  simp only [canonicalIndices, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev CanonicalIndex (d : Fin n → ℕ) (L W k : ℕ) := (s : Finset (Fin n)) × ↥(canonicalIndices d L W k s)

noncomputable def canonicalEmbedding (d : Fin n → ℕ) (L W k : ℕ) (a : CanonicalIndex d L W k) : AmbientIndex n :=
  (FixedWidthPolynomial.vector n W a.2.val, a.1)

theorem canonicalEmbedding_injective (d : Fin n → ℕ) (L W k : ℕ) :
    Function.Injective (canonicalEmbedding d L W k) := by
  rintro ⟨s, a⟩ ⟨t, b⟩ h
  have hst := congrArg Prod.snd h
  change s = t at hst
  subst t
  apply congrArg (Sigma.mk s)
  apply Subtype.ext
  exact FixedWidthPolynomial.vector_injective n W (congrArg Prod.fst h)

noncomputable def canonicalGenerator (d : Fin n → ℕ) (L W k : ℕ) (a : CanonicalIndex d L W k) : Total n R :=
  ambientBasis (canonicalEmbedding d L W k a)

theorem canonicalGenerator_apply (d : Fin n → ℕ) (L W k : ℕ) (a : CanonicalIndex d L W k) :
    canonicalGenerator (R := R) d L W k a =
      MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val) (1 : R) • exteriorBasis (R := R) a.1 :=
  ambientBasis_apply _ _

theorem canonicalGenerator_independent (d : Fin n → ℕ) (L W k : ℕ) :
    LinearIndependent R (canonicalGenerator (R := R) d L W k) :=
  (ambientBasis (R := R)).linearIndependent.comp _ (canonicalEmbedding_injective d L W k)

noncomputable def canonicalSpan (d : Fin n → ℕ) (L W k : ℕ) : Submodule R (Total n R) :=
  Submodule.span R (Set.range (canonicalGenerator (R := R) d L W k))

theorem canonicalGenerator_mem_space (d : Fin n → ℕ) (L W k : ℕ) (a : CanonicalIndex d L W k) :
    canonicalGenerator (R := R) d L W k a ∈ space (R := R) d L W k := by
  have ha := (mem_canonicalIndices d L W k a.1 a.2.val).mp a.2.property
  have hr : a.2.val ∈ indices d L W k (a.1.orderEmbOfFin ha.1) := by
    rw [mem_indices, wordWeight_ordered]
    exact ha.2
  rw [canonicalGenerator_apply, exteriorBasis_as_blade a.1 ha.1]
  exact generator_mem d L W k ⟨a.1.orderEmbOfFin ha.1, a.2.val, hr⟩

theorem canonicalSpan_le_space (d : Fin n → ℕ) (L W k : ℕ) :
    canonicalSpan (R := R) d L W k ≤ space (R := R) d L W k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact canonicalGenerator_mem_space d L W k a

end LeanCanny.Algebra.KoszulWeighted
