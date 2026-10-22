/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayGenericShift
public import LeanCanny.Algebra.KoszulComplex
public import Mathlib.RingTheory.Localization.Away.Basic

/-! # Exact Koszul complexes on the generic coordinate charts

The Macaulay certificates put a power of each variable in the generic shifted
ideal. After inverting any coordinate, this gives a unit combination of the
shifted inputs. Their Koszul differential is therefore contractible and
exact in every exterior degree. This is coordinate-localized exactness;
the finite weighted polynomial grade is a separate construction.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ} {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]

theorem genericShift_unitCombination_of_isUnit (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (i : Fin n) (φ : MvPolynomial (Fin n) (RatFunc R) →+* S) (hi : IsUnit (φ (MvPolynomial.X i))) :
    ∃ v : Fin n → S, ∑ j, v j * φ (genericShift p d j) = 1 := by
  have hmem : (MvPolynomial.X i : MvPolynomial (Fin n) (RatFunc R)) ^ level d ∈
      Ideal.span (Set.range (genericShift p d)) := by
    rw [MvPolynomial.X_pow_eq_monomial]
    exact genericShift_monomial_mem_span p d W hp hW _ (Finsupp.degree_single _ _)
  obtain ⟨q, hq⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hsum : (∑ j, φ (q j) * φ (genericShift p d j)) = φ (MvPolynomial.X i) ^ level d := by
    simpa only [map_sum, map_mul, map_pow] using congrArg φ hq
  obtain ⟨a, ha⟩ := (hi.pow (level d)).exists_left_inv
  refine ⟨fun j => a * φ (q j), ?_⟩
  calc
    _ = a * ∑ j, φ (q j) * φ (genericShift p d j) := by rw [Finset.mul_sum]; simp only [mul_assoc]
    _ = 1 := by rw [hsum, ha]

abbrev CoordinateRing (n : ℕ) (R : Type*) [CommRing R] [IsDomain R] (i : Fin n) :=
  Localization.Away (MvPolynomial.X i : MvPolynomial (Fin n) (RatFunc R))

noncomputable def localizedSystem (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    Fin n → CoordinateRing n R i :=
  fun j => algebraMap (MvPolynomial (Fin n) (RatFunc R)) (CoordinateRing n R i) (genericShift p d j)

theorem localized_unitCombination (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W) (i : Fin n) :
    ∃ v : Fin n → CoordinateRing n R i, ∑ j, v j * localizedSystem p d i j = 1 :=
  genericShift_unitCombination_of_isUnit p d W hp hW i
    (algebraMap (MvPolynomial (Fin n) (RatFunc R)) (CoordinateRing n R i))
    (IsLocalization.Away.algebraMap_isUnit _)

theorem localized_graded_exact (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (i : Fin n) (k : ℕ) :
    LinearMap.ker (KoszulExterior.gradedDifferential (localizedSystem p d i) k) =
      LinearMap.range (KoszulExterior.gradedDifferential (localizedSystem p d i) (k + 1)) := by
  obtain ⟨v, hv⟩ := localized_unitCombination p d W hp hW i
  exact KoszulExterior.graded_exact _ v hv k

theorem localized_complex_exact (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W)
    (i : Fin n) (k : ℕ) :
    LinearMap.ker ((KoszulExterior.complex (localizedSystem p d i)).d (k + 1) k).hom =
      LinearMap.range ((KoszulExterior.complex (localizedSystem p d i)).d (k + 2) (k + 1)).hom := by
  obtain ⟨v, hv⟩ := localized_unitCombination p d W hp hW i
  exact KoszulExterior.complex_exact _ v hv k

theorem localized_graded_zero_surjective (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W) (i : Fin n) :
    Function.Surjective (KoszulExterior.gradedDifferential (localizedSystem p d i) 0) := by
  obtain ⟨v, hv⟩ := localized_unitCombination p d W hp hW i
  exact KoszulExterior.graded_zero_surjective _ v hv

theorem localized_homotopy (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : level d < 2 ^ W) (i : Fin n) :
    ∃ v : Fin n → CoordinateRing n R i, ∀ x : KoszulExterior.Total (CoordinateRing n R i) (Fin n),
      KoszulExterior.differential (localizedSystem p d i) (KoszulExterior.wedge v x) +
        KoszulExterior.wedge v (KoszulExterior.differential (localizedSystem p d i) x) = x := by
  obtain ⟨v, hv⟩ := localized_unitCombination p d W hp hW i
  refine ⟨v, fun x => ?_⟩
  have h := KoszulExterior.homotopy_identity (localizedSystem p d i) v x
  change _ = (∑ j, v j * localizedSystem p d i j) • x at h
  simpa only [hv, one_smul] using h

end LeanCanny.Algebra.Macaulay
