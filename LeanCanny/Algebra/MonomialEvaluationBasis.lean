/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Finset.Powerset
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.MvPolynomial.Basic

/-! # Sparse monomials in a finite-dimensional evaluation algebra

Keep a monomial exactly when its image is independent of all earlier images.
These standard monomials span the same space as all monomials and are closed
under divisibility. Every subset of a standard monomial's support is therefore
independent, bounding its support logarithmically in the ambient dimension.

This is a mathematical spanning bound, not yet a native basis-selection program.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonomialEvaluationBasis
open Submodule
open scoped Classical

private theorem indep_of_prior {ι K V : Type*} [LinearOrder ι] [Field K]
    [AddCommGroup V] [Module K V] (v : ι → V) (s : Set ι)
    (h : ∀ i ∈ s, v i ∉ span K (v '' {j | j < i})) : LinearIndepOn K v s := by
  apply linearIndepOn_of_finite s
  intro t hts ht
  have H : ∀ u : Finset ι, (↑u : Set ι) ⊆ s → LinearIndepOn K v (↑u : Set ι) := by
    intro u
    induction u using Finset.induction_on_max with
    | empty => intro _; simp
    | insert a u hmax ih =>
      intro hu
      have ha : a ∉ (↑u : Set ι) := fun ha => lt_irrefl a (hmax a ha)
      rw [Finset.coe_insert, linearIndepOn_insert ha]
      refine ⟨ih (fun i hi => hu (Finset.mem_insert_of_mem hi)), ?_⟩
      intro hm
      apply h a (hu (Finset.mem_insert_self a u))
      exact span_mono (Set.image_mono (fun i hi => hmax i hi)) hm
  simpa only [ht.coe_toFinset] using H ht.toFinset (by simpa only [ht.coe_toFinset] using hts)

variable {σ K A : Type*} [Field K] [CommRing A] [Algebra K A]

noncomputable def vector (φ : MvPolynomial σ K →ₐ[K] A) (d : σ →₀ ℕ) : A :=
  φ (MvPolynomial.monomial d 1)

theorem vector_add (φ : MvPolynomial σ K →ₐ[K] A) (d e : σ →₀ ℕ) :
    vector φ (d + e) = vector φ d * vector φ e := by
  simp only [vector, ← map_mul, MvPolynomial.monomial_mul_monomial, one_mul]

noncomputable def standard (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A) (d : σ →₀ ℕ) : Prop :=
  vector φ d ∉ span K (vector φ '' {e | m.toSyn e < m.toSyn d})

theorem independent (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A) :
    LinearIndependent K (fun d : {d // standard m φ d} => vector φ d.val) := by
  let : LinearOrder (σ →₀ ℕ) := LinearOrder.lift' m.toSyn m.toSyn.injective
  exact indep_of_prior (vector φ) {d | standard m φ d} (fun _ hd => hd)

theorem monomial_mem_span (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A) (d : σ →₀ ℕ) :
    vector φ d ∈ span K (vector φ '' {e | standard m φ e}) := by
  have hw : WellFounded (fun a b : σ →₀ ℕ => m.toSyn a < m.toSyn b) :=
    InvImage.wf m.toSyn wellFounded_lt
  induction d using hw.induction with
  | h d ih =>
    by_cases hd : standard m φ d
    · exact subset_span ⟨d, hd, rfl⟩
    · have hm : vector φ d ∈ span K (vector φ '' {e | m.toSyn e < m.toSyn d}) := not_not.mp hd
      apply (span_le.mpr ?_) hm
      rintro _ ⟨e, he, rfl⟩
      exact ih e he

theorem image_mem_span (φ : MvPolynomial σ K →ₐ[K] A) (p : MvPolynomial σ K) :
    φ p ∈ span K (Set.range (vector φ)) := by
  rw [p.as_sum, map_sum]
  apply sum_mem
  intro d _
  have he : MvPolynomial.monomial d (p.coeff d) = p.coeff d • MvPolynomial.monomial d 1 := by
    simp only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul]
  exact smul_mem _ _ (subset_span ⟨d, rfl⟩)

theorem downward (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A)
    {d e : σ →₀ ℕ} (hd : standard m φ d) (he : e ≤ d) : standard m φ e := by
  intro hn
  let L : A →ₗ[K] A := LinearMap.mul K A (vector φ (d - e))
  have hmap : span K (vector φ '' {z | m.toSyn z < m.toSyn e}) ≤
      (span K (vector φ '' {z | m.toSyn z < m.toSyn d})).comap L := by
    apply span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    change vector φ (d - e) * vector φ z ∈ span K (vector φ '' {z | m.toSyn z < m.toSyn d})
    rw [← vector_add]
    apply subset_span
    refine ⟨d - e + z, ?_, rfl⟩
    calc
      m.toSyn (d - e + z) < m.toSyn (d - e + e) := by
        simpa only [map_add, add_comm] using add_lt_add_left hz (m.toSyn (d - e))
      _ = m.toSyn d := congrArg m.toSyn (tsub_add_cancel_of_le he)
  have hmem := hmap hn
  change vector φ (d - e) * vector φ e ∈ span K (vector φ '' {z | m.toSyn z < m.toSyn d}) at hmem
  rw [← vector_add, tsub_add_cancel_of_le he] at hmem
  exact hd hmem

noncomputable def subsetExponent (s : Finset σ) : σ →₀ ℕ := Finsupp.indicator s (fun _ _ => 1)

theorem support_subsetExponent (s : Finset σ) : (subsetExponent s).support = s := by
  ext i
  simp only [subsetExponent, Finsupp.mem_support_iff, Finsupp.indicator_apply]
  split_ifs <;> simp_all

theorem subsetExponent_injective : Function.Injective (subsetExponent (σ := σ)) := by
  intro s t h
  simpa only [support_subsetExponent] using congrArg Finsupp.support h

theorem subsetExponent_le {s : Finset σ} {d : σ →₀ ℕ} (h : s ⊆ d.support) : subsetExponent s ≤ d := by
  intro i
  simp only [subsetExponent, Finsupp.indicator_apply]
  split_ifs with hi
  · exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (h hi))
  · exact Nat.zero_le _

theorem support_bound [Module.Finite K A] (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A)
    {d : σ →₀ ℕ} (hd : standard m φ d) : 2 ^ d.support.card ≤ Module.finrank K A := by
  let f : {s : Finset σ // s ∈ d.support.powerset} → {e // standard m φ e} :=
    fun s => ⟨subsetExponent s.val, downward m φ hd (subsetExponent_le (Finset.mem_powerset.mp s.property))⟩
  have hf : Function.Injective f := by
    intro s t h
    exact Subtype.ext (subsetExponent_injective (congrArg Subtype.val h))
  have hI := (independent m φ).comp f hf
  simpa only [Fintype.card_coe, Finset.card_powerset] using hI.fintype_card_le_finrank

theorem exponent_bound (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A)
    (hcube : ∀ i, φ (MvPolynomial.X i) ^ 3 = φ (MvPolynomial.X i))
    {d : σ →₀ ℕ} (hd : standard m φ d) (i : σ) : d i ≤ 2 := by
  by_contra hi
  have hs : standard m φ (Finsupp.single i 3) :=
    downward m φ hd (Finsupp.single_le_iff.mpr (by omega))
  have he : vector φ (Finsupp.single i 3) = vector φ (Finsupp.single i 1) := by
    simp only [vector, ← MvPolynomial.X_pow_eq_monomial, map_pow, pow_one]
    exact hcube i
  apply hs
  rw [he]
  apply subset_span
  refine ⟨Finsupp.single i 1, ?_, rfl⟩
  apply m.toSyn_strictMono
  apply lt_of_le_of_ne (Finsupp.single_mono (i := i) (by decide : 1 ≤ 3))
  intro h
  have h' := congrArg (fun e : σ →₀ ℕ => e i) h
  simp only [Finsupp.single_eq_same] at h'
  omega

/-- A feature family can be exponentially long while its spanning monomials
use only `w` features, each to exponent at most two. -/
theorem sparse_span [Module.Finite K A] (m : MonomialOrder σ) (φ : MvPolynomial σ K →ₐ[K] A)
    (w : ℕ) (hdim : Module.finrank K A ≤ 2 ^ w)
    (hcube : ∀ i, φ (MvPolynomial.X i) ^ 3 = φ (MvPolynomial.X i)) :
    span K (Set.range (vector φ)) =
      span K (vector φ '' {d | d.support.card ≤ w ∧ ∀ i, d i ≤ 2}) := by
  apply le_antisymm
  · apply span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply (span_mono ?_) (monomial_mem_span m φ d)
    apply Set.image_mono
    intro e he
    exact ⟨(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ((support_bound m φ he).trans hdim),
      exponent_bound m φ hcube he⟩
  · exact span_mono (Set.image_subset_range _ _)

end LeanCanny.Algebra.MonomialEvaluationBasis
