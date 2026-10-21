/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayMinorCross
public import LeanCanny.Algebra.MacaulayFullPermutation

/-! # The polynomial quotient divides every full Macaulay maximal minor

The cross identity represents the quotient of a maximal minor by the
universal polynomial using each higher denominator. Their omitted groups
and common normalization force that fraction to be a polynomial. Integer
coefficient specialization then gives divisibility over every commutative
ring, including singular specializations of the extraneous matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem integerQuotient_dvd_fullMinor (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W) :
    integerQuotient d W hdegree hW ∣ fullMinor (R := ℤ) d W (Equiv.refl _) f := by
  let P := CoefficientRing (n + 1) ℤ
  let F := FractionRing P
  let φ : P →+* F := algebraMap P F
  let m : P := fullMinor d W (Equiv.refl _) f
  let q : P := integerQuotient d W hdegree hW
  let b := higherDenominatorFamily (R := ℤ) d W hW
  let a := fun i : Fin (n + 1) => Macaulay.minorRelationFactor (system (R := ℤ) d W (orderingFor i)) (d ∘ orderingFor i) W
    (by rwa [level_comp_perm]) (Macaulay.transportSelector d W (orderingFor i) f)
  have hinj : Function.Injective φ := FaithfulSMul.algebraMap_injective P F
  have hq : φ q ≠ 0 := fun hz => integerQuotient_ne_zero d W hdegree hW (hinj (hz.trans (map_zero φ).symm))
  have hcross (i : Fin (n + 1)) : m * b i = q * a i := by
    have he := fullMinor_quotient_cross d W hdegree hW (orderingFor i) (by rwa [level_comp_perm])
      (Macaulay.transportSelector d W (orderingFor i) f)
    have hm : fullMinor (R := ℤ) d W (orderingFor i) (Macaulay.transportSelector d W (orderingFor i) f) = m :=
      fullMinor_ordering d W (orderingFor i) f
    rw [hm] at he
    exact he
  let x : F := φ m / φ q
  have hrep (i : Fin (n + 1)) : x * φ (b i) = φ (a i) := by
    dsimp only [x]
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff hq).mpr
    simpa only [map_mul] using congrArg φ ((hcross i).trans (mul_comm _ _))
  obtain ⟨c, hc⟩ := GroupedDenominatorCancellation.isPolynomial_of_omitted_groups Prod.fst a b
    (higherDenominatorFamily_omits d W hW) (powerPoint (R := ℤ) d)
    (higherDenominatorFamily_power_specialization d W hdegree hW) x hrep
  refine ⟨c, ?_⟩
  apply hinj
  rw [map_mul, hc]
  change φ m = φ q * (φ m / φ q)
  rw [mul_comm, div_mul_cancel₀ _ hq]

theorem fullMinor_map_coefficients (φ : R →+* S) (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (f : Macaulay.activeIndices (d ∘ π) W → Macaulay.MultiplierIndex (d ∘ π) W) :
    MvPolynomial.map φ (fullMinor (R := R) d W π f) = fullMinor (R := S) d W π f := by
  rw [fullMinor, RingHom.map_det]
  change (((Macaulay.fullMatrix (system (R := R) d W π) (d ∘ π) W).map (MvPolynomial.map φ)).submatrix f id).det = _
  rw [Macaulay.fullMatrix_map]
  have hs : (fun i => (system (R := R) d W π i).map (MvPolynomial.map φ)) = system (R := S) d W π :=
    funext (system_map_coefficients φ d W π)
  rw [hs]
  rfl

theorem specialize_fullMinor (d : Fin n → ℕ) (W : ℕ) (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W)
    (f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W) :
    MvPolynomial.eval (fun v => (p v.1).coeff v.2) (fullMinor (R := R) d W (Equiv.refl _) f) =
      ((Macaulay.fullMatrix p d W).submatrix f id).det := by
  change MvPolynomial.eval (fun v : CoefficientIndex n => (p v.1).coeff v.2)
    (((Macaulay.fullMatrix (system (R := R) d W (Equiv.refl _)) d W).submatrix f id).det) = _
  rw [RingHom.map_det]
  change (((Macaulay.fullMatrix (system (R := R) d W (Equiv.refl _)) d W).map
    (MvPolynomial.eval (fun v => (p v.1).coeff v.2))).submatrix f id).det = _
  rw [Macaulay.fullMatrix_map]
  have hs : (fun i => (system (R := R) d W (Equiv.refl _) i).map (MvPolynomial.eval (fun v => (p v.1).coeff v.2))) = p :=
    funext (specialize_system_of_level d W p hp hd hW)
  rw [hs]

theorem coefficientSpecialization_fullMinor (d : Fin (n + 1) → ℕ) (W : ℕ)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i))
    (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W)
    (f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W) :
    coefficientSpecialization p (fullMinor (R := ℤ) d W (Equiv.refl _) f) = ((Macaulay.fullMatrix p d W).submatrix f id).det := by
  change MvPolynomial.eval₂ (Int.castRingHom R) (fun v : CoefficientIndex (n + 1) => (p v.1).coeff v.2) _ = _
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact (congrArg (MvPolynomial.eval (fun v : CoefficientIndex (n + 1) => (p v.1).coeff v.2))
    (fullMinor_map_coefficients (Int.castRingHom R) d W (Equiv.refl _) f)).trans (specialize_fullMinor d W p hp hd hW f)

theorem polynomialValue_dvd_fullMinor (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (f : Macaulay.activeIndices d W → Macaulay.MultiplierIndex d W) :
    polynomialValue d W hdegree hW p ∣ ((Macaulay.fullMatrix p d W).submatrix f id).det := by
  obtain ⟨c, hc⟩ := integerQuotient_dvd_fullMinor d W hdegree hW f
  refine ⟨coefficientSpecialization p c, ?_⟩
  have he := congrArg (coefficientSpecialization p) hc
  rw [coefficientSpecialization_fullMinor d W p hp hd hW, map_mul] at he
  exact he

end LeanCanny.Algebra.MacaulayUniversal
