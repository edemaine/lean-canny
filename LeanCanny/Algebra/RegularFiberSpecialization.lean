/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteFiberSpecialization
public import Mathlib.RingTheory.Ideal.Maximal

/-! # Exceptional parameter polynomials for regular root fibers

If a polynomial root system has no singular solution over any extension of
the generic parameter field, denominator clearing gives a nonzero parameter
factor outside which every specialized root is regular. The factor is derived
from an ideal identity; it is not an oracle for critical values. No degree or
coefficient-size bound on that identity is asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.RegularFiberSpecialization
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

universe u
variable {A F ι κ : Type u} [CommRing A] [IsDomain A]
  [Field F] [Algebra A F] [IsFractionRing A F]

/-- An ideal that becomes the unit ideal generically contains a nonzero
parameter scalar before passing to the fraction field. -/
theorem exists_scalar_mem (I : Ideal (MvPolynomial ι A))
    (hI : I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F)) = ⊤) :
    ∃ s : A, s ≠ 0 ∧ C s ∈ I := by
  have hmem : algebraMap (MvPolynomial ι A) (MvPolynomial ι F) 1 ∈
      I.map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F)) := by rw [hI]; trivial
  obtain ⟨m, hmM, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors A).map (C (σ := ι))) (MvPolynomial ι F) I 1).mp hmem
  obtain ⟨s, hs, rfl⟩ := hmM
  exact ⟨s, nonZeroDivisors.ne_zero hs, by simpa only [mul_one] using hmI⟩

noncomputable def badIdeal (q : κ → MvPolynomial ι A) (D : MvPolynomial ι A) :
    Ideal (MvPolynomial ι A) := Ideal.span (insert D (Set.range q))

omit [IsDomain A] [IsFractionRing A F] in
/-- A universal generic regularity statement forces the singularity ideal to
be the unit ideal. The witness field in the proof is a prime quotient's
fraction field; no algebraic-closure or real-root assumption is used. -/
theorem map_badIdeal_eq_top (q : κ → MvPolynomial ι A) (D : MvPolynomial ι A)
    (hregular : ∀ (L : Type u) [Field L] [Algebra F L] (x : ι → L),
      (∀ i, aeval x ((q i).map (algebraMap A F)) = 0) →
        aeval x (D.map (algebraMap A F)) ≠ 0) :
    (badIdeal q D).map (algebraMap (MvPolynomial ι A) (MvPolynomial ι F)) = ⊤ := by
  by_contra htop
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ htop
  let : P.IsMaximal := hP
  let : P.IsPrime := hP.isPrime
  let L := FractionRing (MvPolynomial ι F ⧸ P)
  let x : ι → L := FiniteAlgebraicZeros.quotientPoint P
  have hzero (p : MvPolynomial ι A) (hp : p ∈ badIdeal q D) :
      aeval x (p.map (algebraMap A F)) = 0 := by
    rw [FiniteAlgebraicZeros.eval_quotientPoint]
    have hmem : p.map (algebraMap A F) ∈ P := hle (Ideal.mem_map_of_mem _ hp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  have hq (i : κ) : aeval x ((q i).map (algebraMap A F)) = 0 :=
    hzero (q i) (Ideal.subset_span (Set.mem_insert_of_mem D (Set.mem_range_self i)))
  exact hregular L x hq (hzero D (Ideal.subset_span (Set.mem_insert D _)))

/-- A nonzero parameter factor excludes all singular roots after specialization.
This works over every target field, so in particular over the real numbers. -/
theorem exists_exceptional (q : κ → MvPolynomial ι A) (D : MvPolynomial ι A)
    (hregular : ∀ (L : Type u) [Field L] [Algebra F L] (x : ι → L),
      (∀ i, aeval x ((q i).map (algebraMap A F)) = 0) →
        aeval x (D.map (algebraMap A F)) ≠ 0) :
    ∃ s : A, s ≠ 0 ∧ ∀ (L : Type u) [Field L] (φ : A →+* L) (x : ι → L),
      φ s ≠ 0 → (∀ i, (q i).eval₂ φ x = 0) → D.eval₂ φ x ≠ 0 := by
  obtain ⟨s, hs, hmem⟩ := exists_scalar_mem (badIdeal q D) (map_badIdeal_eq_top q D hregular)
  refine ⟨s, hs, ?_⟩
  intro L _ φ x hφ hx hD
  have hker : badIdeal q D ≤ RingHom.ker (MvPolynomial.eval₂Hom φ x) := by
    apply Ideal.span_le.mpr
    rintro p (rfl | ⟨i, rfl⟩)
    · exact hD
    · exact hx i
  have hz := hker hmem
  change (C s : MvPolynomial ι A).eval₂ φ x = 0 at hz
  exact hφ (by simpa only [eval₂_C] using hz)

end LeanCanny.Algebra.RegularFiberSpecialization
