/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.NestedPolynomial
public import LeanCanny.Algebra.FixedWidthPolynomialLayout

/-! # Spatial coefficient slices of a polynomial with parameter variables

A slice is an actual coefficient polynomial in the parameter block. An indexed
monomial source supplies it by filtering spatial exponents, before any parameter
substitution. No expanded coefficient polynomial is needed by the reader.
-/

@[expose] public section

namespace LeanCanny.Algebra.PartialCoefficient
open MvPolynomial
open scoped BigOperators Classical

variable {σ τ R : Type*} [CommRing R]

noncomputable def leftExponent (m : Sum σ τ →₀ ℕ) : σ →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp m).1

noncomputable def rightExponent (m : Sum σ τ →₀ ℕ) : τ →₀ ℕ :=
  (Finsupp.sumFinsuppAddEquivProdFinsupp m).2

@[simp] theorem leftExponent_apply (m : Sum σ τ →₀ ℕ) (i : σ) : leftExponent m i = m (.inl i) := rfl
@[simp] theorem rightExponent_apply (m : Sum σ τ →₀ ℕ) (i : τ) : rightExponent m i = m (.inr i) := rfl

noncomputable def slice (p : MvPolynomial (Sum σ τ) R) (e : σ →₀ ℕ) : MvPolynomial τ R :=
  (sumRingEquiv R σ τ p).coeff e

theorem sumRingEquiv_monomial (m : Sum σ τ →₀ ℕ) (a : R) :
    sumRingEquiv R σ τ (monomial m a) = monomial (leftExponent m) (monomial (rightExponent m) a) := by
  simp only [sumRingEquiv, RingEquiv.trans_apply, monomial, AddMonoidAlgebra.lsingle_apply,
    AddMonoidAlgebra.mapDomainRingEquiv_single]
  exact AddMonoidAlgebra.curryRingEquiv_single (leftExponent m) (rightExponent m) a

theorem slice_monomial (m : Sum σ τ →₀ ℕ) (a : R) (e : σ →₀ ℕ) :
    slice (monomial m a) e = if leftExponent m = e then monomial (rightExponent m) a else 0 := by
  rw [slice, sumRingEquiv_monomial, coeff_monomial]

theorem slice_sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial (Sum σ τ) R) (e : σ →₀ ℕ) :
    slice (∑ i ∈ s, p i) e = ∑ i ∈ s, slice (p i) e := by
  simp only [slice, map_sum, MvPolynomial.coeff_sum]

theorem slice_flatten (p : MvPolynomial σ (MvPolynomial τ R)) (e : σ →₀ ℕ) :
    slice (NestedPolynomial.flatten p) e = p.coeff e := by
  change (sumRingEquiv R σ τ ((sumRingEquiv R σ τ).symm p)).coeff e = _
  rw [RingEquiv.apply_symm_apply]

theorem specialize_coefficient {S : Type*} [CommRing S] (φ : MvPolynomial τ R →+* S)
    (p : MvPolynomial σ (MvPolynomial τ R)) (e : σ →₀ ℕ) :
    (p.map φ).coeff e = φ (slice (NestedPolynomial.flatten p) e) := by
  rw [slice_flatten, MvPolynomial.coeff_map]



theorem coeff_rename_native {ι : Type*} [Fintype σ] [Fintype ι] (N W r : ℕ)
    (f : σ ≃ ι) (g : σ ≃ Fin N) (p : MvPolynomial σ R) :
    (MvPolynomial.rename f p).coeff (FixedWidthPolynomial.nativeExponent (f.symm.trans g) W r) =
      p.coeff (FixedWidthPolynomial.nativeExponent g W r) := by
  have he : (FixedWidthPolynomial.nativeExponent g W r).mapDomain f =
      FixedWidthPolynomial.nativeExponent (f.symm.trans g) W r := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, FixedWidthPolynomial.nativeExponent,
      Finsupp.coe_equivFunOnFinite_symm, Equiv.trans_apply]
  rw [← he, MvPolynomial.coeff_rename_mapDomain f f.injective]

theorem native_sum [Fintype σ] (N W : ℕ) (f : σ ≃ Fin N) (p : MvPolynomial σ R)
    (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) :
    ∑ r ∈ Finset.range (FixedWidthPolynomial.count N W),
      monomial (FixedWidthPolynomial.nativeExponent f W r) (p.coeff (FixedWidthPolynomial.nativeExponent f W r)) = p := by
  apply MvPolynomial.rename_injective f f.injective
  rw [map_sum]
  simp only [MvPolynomial.rename_monomial, FixedWidthPolynomial.nativeExponent_map]
  have hs := FixedWidthPolynomial.indexed_source_eq N W (MvPolynomial.rename f p) (by
    intro m hm i
    rw [MvPolynomial.support_rename_of_injective f.injective] at hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
    have he : u.mapDomain f i = u (f.symm i) := by
      rw [Finsupp.mapDomain_equiv_apply]
    rw [he]
    exact hp u hu _)
  simpa only [RationalSubstitution.Indexed.source, FixedWidthPolynomial.coeff_rename_rank] using hs

theorem slice_native_sum [Fintype σ] [Fintype τ] (N W : ℕ) (f : Sum σ τ ≃ Fin N)
    (p : MvPolynomial (Sum σ τ) R) (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) (e : σ →₀ ℕ) :
    ∑ r ∈ Finset.range (FixedWidthPolynomial.count N W),
      monomial (rightExponent (FixedWidthPolynomial.nativeExponent f W r))
        (if leftExponent (FixedWidthPolynomial.nativeExponent f W r) = e
          then p.coeff (FixedWidthPolynomial.nativeExponent f W r) else 0) = slice p e := by
  have h := congrArg (fun q => slice q e) (native_sum N W f p hp)
  rw [slice_sum] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  rw [slice_monomial]
  split_ifs <;> simp only [map_zero]


theorem slice_source_eq [Fintype σ] [Fintype τ] (N A B W : ℕ)
    (f : Sum σ τ ≃ Fin N) (g : σ ≃ Fin A) (h : τ ≃ Fin B)
    (hr : ∀ i, (f (.inr i)).val = A + (h i).val)
    (p : MvPolynomial (Sum σ τ) R) (hp : ∀ m ∈ p.support, ∀ i, m i < 2 ^ W) (s : ℕ) :
    RationalSubstitution.Indexed.source B (FixedWidthPolynomial.count N W)
      (fun r => if leftExponent (FixedWidthPolynomial.nativeExponent f W r) = FixedWidthPolynomial.nativeExponent g W s
        then p.coeff (FixedWidthPolynomial.nativeExponent f W r) else 0)
      (fun r i => FixedWidthPolynomial.entry W r (A + i)) =
      MvPolynomial.rename h (slice p (FixedWidthPolynomial.nativeExponent g W s)) := by
  rw [← slice_native_sum N W f p hp, map_sum]
  unfold RationalSubstitution.Indexed.source
  apply Finset.sum_congr rfl
  intro r _
  rw [MvPolynomial.rename_monomial]
  have he : (rightExponent (FixedWidthPolynomial.nativeExponent f W r)).mapDomain h =
      RationalSubstitution.Indexed.exponentVector B (fun i => FixedWidthPolynomial.entry W r (A + i)) := by
    ext i
    simp only [Finsupp.mapDomain_equiv_apply, rightExponent_apply, FixedWidthPolynomial.nativeExponent,
      Finsupp.coe_equivFunOnFinite_symm, hr, Equiv.apply_symm_apply, RationalSubstitution.Indexed.exponentVector]
  rw [he]

end LeanCanny.Algebra.PartialCoefficient
