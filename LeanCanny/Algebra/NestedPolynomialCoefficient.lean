/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PartialCoefficient
/-! # Exact scalar coefficients after flattening a coefficient-variable block -/
@[expose] public section
namespace LeanCanny.Algebra.NestedPolynomial
open MvPolynomial
open scoped Classical
variable {σ τ R : Type*} [CommRing R]

noncomputable def joinExponent (e : σ →₀ ℕ) (f : τ →₀ ℕ) : Sum σ τ →₀ ℕ :=
  Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, f)

theorem joinExponent_eq_iff (a e : σ →₀ ℕ) (b f : τ →₀ ℕ) :
    joinExponent a b = joinExponent e f ↔ a = e ∧ b = f := by
  change Finsupp.sumFinsuppAddEquivProdFinsupp.symm (a, b) =
    Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, f) ↔ _
  rw [Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective.eq_iff]
  simp only [Prod.mk.injEq]

theorem flatten_monomial_monomial (e : σ →₀ ℕ) (f : τ →₀ ℕ) (a : R) :
    flatten (monomial e (monomial f a)) = monomial (joinExponent e f) a := by
  apply (sumRingEquiv R σ τ).injective
  change (sumRingEquiv R σ τ) ((sumRingEquiv R σ τ).symm _) = _
  rw [RingEquiv.apply_symm_apply,
    PartialCoefficient.sumRingEquiv_monomial]
  have HE := Finsupp.sumFinsuppAddEquivProdFinsupp.apply_symm_apply (e, f)
  have HL : PartialCoefficient.leftExponent (joinExponent e f) = e := congrArg Prod.fst HE
  have HR : PartialCoefficient.rightExponent (joinExponent e f) = f := congrArg Prod.snd HE
  rw [HL, HR]

theorem coefficient (p : MvPolynomial σ (MvPolynomial τ R)) (e : σ →₀ ℕ) (f : τ →₀ ℕ) :
    (flatten p).coeff (joinExponent e f) = (p.coeff e).coeff f := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | monomial a c =>
    induction c using MvPolynomial.induction_on' with
    | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
    | monomial b c =>
      rw [flatten_monomial_monomial, coeff_monomial, coeff_monomial]
      by_cases ha : a = e <;> by_cases hb : b = f <;>
        simp [joinExponent_eq_iff, ha, hb]

end LeanCanny.Algebra.NestedPolynomial
