/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRetainedRealBound
public import LeanCanny.Geometry.FixedLeadingDilationValueBound
/-! # A level capacity chosen from the existing correlated bank

Current integer multiplication-matrix bounds first bound the actual retained
real quotients. The next level coefficient is then chosen. It has not entered
the old source, old bank or old bound. Frozen original coordinates are unscaled;
no old Y coordinate or old level value is reused.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
open LeanCanny.Algebra IntegralMixedHistory IntegralMixedRetainedRealBound
open FixedLeadingDilationValueBound Filter
open scoped Topology
variable {n p S B m G : ℕ} {P : SpatialSource p} {ι : Type}

def exponent (n D R G : ℕ) : ℕ := n.size+height R G*FixedLeadingTiltedSource.degree D+2

def coefficient (n D R G : ℕ) : ℤ := 2^exponent n D R G

theorem coefficient_eq (n D R G : ℕ) : coefficient n D R G=levelCoefficient n D (height R G) := rfl

theorem frozen_margin (x : State P S B m ι) (HG : x.bank.Bounds G)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (k D : ℕ) (select : Fin k → Fin m)
    (a : Fin n → ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k,
      a i=φ (x.bank.numerator (select ⟨i.val,hi⟩))/(x.bank.denominator (select ⟨i.val,hi⟩):ℝ)) :
    |frozenValue k D a| < (coefficient n D (FixedWidthPolynomial.count m B) G:ℝ)-1 := by
  apply FixedLeadingDilationValueBound.frozen_margin k D (height (FixedWidthPolynomial.count m B) G) a
  intro i hi
  rw [Hparam i hi]
  exact quotient x HG φ _

theorem frozen_margin_correlated (x : State P S B m ι) (HG : x.bank.Bounds G)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (k D : ℕ) (select : Fin k → Fin m) (a : Fin n → ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k, a i=values (select ⟨i.val,hi⟩)) :
    |frozenValue k D a| < (coefficient n D (FixedWidthPolynomial.count m B) G:ℝ)-1 := by
  apply frozen_margin x HG φ k D select a
  intro i hi
  exact (Hparam i hi).trans (H _).symm

theorem eventually_level_critical {I : Type*} (l : Filter I)
    (x : State P S B m ι) (HG : x.bank.Bounds G)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (k D : ℕ) (select : Fin k → Fin m)
    (u : Fin n) (t : LeanCanny.ETR.Term) (ht : t.degreeBound ≤ D)
    (ha : t.arity ≤ n) (hu : k ≤ u.val) (hD : 0<D)
    (eta : I → ℝ) (original : I → Fin n → ℝ) (a : Fin n → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hx : Tendsto original l (𝓝 a))
    (hne : ∀ᶠ i in l, eta i≠0)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k,
      a i=φ (x.bank.numerator (select ⟨i.val,hi⟩))/(x.bank.denominator (select ⟨i.val,hi⟩):ℝ))
    (hcritical : ∀ᶠ i in l, ∀ j : Fin n, k ≤ j.val →
      (MvPolynomial.pderiv j (FixedLeadingTiltedGradient.tilted k D u t
        (eta i/(commonDenominator x:ℝ)))).eval (original i)=0) :
    ∀ᶠ i in l, ∃ v ∈ Set.Icc (-1:ℝ) 1,
      (FermatLevelLift.polynomial (FermatLevelLift.source (FixedLeadingTiltedSource.source k D u t ht)
        (coefficient n D (FixedWidthPolynomial.count m B) G))).eval₂ (Int.castRingHom ℝ)
        (Fin.snoc (FixedLeadingTiltedGradient.point k (eta i/(commonDenominator x:ℝ)) (original i)) v)=0 ∧
      ∀ j : Fin (n+1), k+1 ≤ j.val →
        (MvPolynomial.pderiv j.castSucc (FermatLevelLift.polynomial (FermatLevelLift.source
          (FixedLeadingTiltedSource.source k D u t ht) (coefficient n D (FixedWidthPolynomial.count m B) G)))).eval₂
          (Int.castRingHom ℝ)
          (Fin.snoc (FixedLeadingTiltedGradient.point k (eta i/(commonDenominator x:ℝ)) (original i)) v)=0 := by
  apply FixedLeadingDilationValueBound.eventually_level_critical l k D (height (FixedWidthPolynomial.count m B) G)
    u t ht ha hu hD eta (commonDenominator x:ℝ) (Int.cast_ne_zero.mpr (commonDenominator_ne_zero x))
    original a heta hx hne _ hcritical
  intro i hi
  rw [Hparam i hi]
  exact quotient x HG φ _

end LeanCanny.Geometry.IntegralMixedCausalLevelCapacity
