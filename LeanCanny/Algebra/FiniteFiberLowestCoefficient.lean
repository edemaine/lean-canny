/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteFiberSaturation
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

/-! # Lowest coefficients vanish on finite affine fibers

If a polynomial vanishes on a system of `n` equations in `n+1` variables,
Krull's height theorem permits cancellation of its deformation-variable
power in the radical ideal when the zero fiber is finite. Its first
possibly nonzero coefficient then vanishes on that fiber. This algebraic
argument covers singular points and supplies no analytic root curve.
-/

@[expose] public section

namespace LeanCanny.Algebra.FiniteFiberLowestCoefficient

open MvPolynomial
open scoped Classical
variable {n : ℕ} {K : Type*} [Field K] [IsAlgClosed K]

noncomputable def encode (q : Polynomial (MvPolynomial (Fin n) K)) : MvPolynomial (Fin (n + 1)) K :=
  (MvPolynomial.finSuccEquiv K n).symm q

omit [IsAlgClosed K] in
theorem eval_encode (q : Polynomial (MvPolynomial (Fin n) K)) (s : K) (z : Fin n → K) :
    MvPolynomial.eval (Fin.cons s z) (encode q) = Polynomial.eval₂ (MvPolynomial.eval z) s q := by
  rw [MvPolynomial.eval_eq_eval_mv_eval', encode, AlgEquiv.apply_symm_apply, Polynomial.eval_map]

omit [IsAlgClosed K] in
theorem finite_fiber_of_finite_zero_set (p : Fin n → MvPolynomial (Fin (n + 1)) K)
    (hf : {z : Fin n → K | ∀ i, MvPolynomial.eval (Fin.cons 0 z) (p i) = 0}.Finite) :
    (zeroLocus K (ProjectiveNullstellensatz.generated p ⊔ Ideal.span {MvPolynomial.X 0})).Finite := by
  apply (hf.image (Fin.cons 0)).subset
  intro x hx
  have hx0 : x 0 = 0 := by
    have he := hx (MvPolynomial.X 0) (show MvPolynomial.X 0 ∈
      ProjectiveNullstellensatz.generated p ⊔ Ideal.span {MvPolynomial.X 0} from
      Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
    simpa only [MvPolynomial.aeval_X] using he
  have hc : Fin.cons 0 (fun j => x j.succ) = x := by
    funext j
    exact Fin.cases hx0.symm (fun _ => rfl) j
  refine ⟨(fun j => x j.succ), ?_, hc⟩
  change ∀ i, MvPolynomial.eval (Fin.cons 0 (fun j => x j.succ)) (p i) = 0
  rw [hc]
  intro i
  have he := hx (p i) (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_range_self i)))
  simpa only [MvPolynomial.aeval_eq_eval] using he

theorem coefficient_vanishes_of_finite_fiber
    (p : Fin n → MvPolynomial (Fin (n + 1)) K) (q : Polynomial (MvPolynomial (Fin n) K)) (k : ℕ)
    (hk : ∀ j < k, q.coeff j = 0)
    (hfinite : (zeroLocus K (ProjectiveNullstellensatz.generated p ⊔ Ideal.span {MvPolynomial.X 0})).Finite)
    (hvanish : ∀ x ∈ zeroLocus K (ProjectiveNullstellensatz.generated p), MvPolynomial.eval x (encode q) = 0)
    (z : Fin n → K) (hz : Fin.cons 0 z ∈ zeroLocus K (ProjectiveNullstellensatz.generated p)) :
    MvPolynomial.eval z (q.coeff k) = 0 := by
  obtain ⟨r, hr⟩ := (Polynomial.X_pow_dvd_iff.mpr hk : (Polynomial.X : Polynomial (MvPolynomial (Fin n) K)) ^ k ∣ q)
  have hr0 : r.coeff 0 = q.coeff k := by
    have he := congrArg (fun f : Polynomial (MvPolynomial (Fin n) K) => f.coeff k) hr
    simpa only [Polynomial.coeff_X_pow_mul', Nat.le_refl, ite_true, Nat.sub_self] using he.symm
  have hm : encode q ∈ (ProjectiveNullstellensatz.generated p).radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    exact hvanish x hx
  have hX : (MvPolynomial.finSuccEquiv K n).symm Polynomial.X = (MvPolynomial.X 0 : MvPolynomial (Fin (n + 1)) K) := by
    apply (MvPolynomial.finSuccEquiv K n).injective
    rw [AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_zero]
  have he : encode q = MvPolynomial.X 0 ^ k * encode r := by
    change (MvPolynomial.finSuccEquiv K n).symm q = _
    rw [hr, map_mul, map_pow, hX]
    rfl
  rw [he] at hm
  have hc := FiniteFiberSaturation.cancel_pow_mul_mem_radical_of_finite_fiber p (MvPolynomial.X 0) (encode r) k hfinite hm
  have hv : MvPolynomial.eval (Fin.cons 0 z) (encode r) = 0 :=
    (MvPolynomial.radical_le_vanishingIdeal_zeroLocus (K := K) (ProjectiveNullstellensatz.generated p) hc) _ hz
  rw [eval_encode, Polynomial.eval₂_at_zero, hr0] at hv
  exact hv

theorem trailingCoeff_vanishes_of_finite_fiber
    (p : Fin n → MvPolynomial (Fin (n + 1)) K) (q : Polynomial (MvPolynomial (Fin n) K))
    (hfinite : (zeroLocus K (ProjectiveNullstellensatz.generated p ⊔ Ideal.span {MvPolynomial.X 0})).Finite)
    (hvanish : ∀ x ∈ zeroLocus K (ProjectiveNullstellensatz.generated p), MvPolynomial.eval x (encode q) = 0)
    (z : Fin n → K) (hz : Fin.cons 0 z ∈ zeroLocus K (ProjectiveNullstellensatz.generated p)) :
    MvPolynomial.eval z q.trailingCoeff = 0 :=
  coefficient_vanishes_of_finite_fiber p q q.natTrailingDegree
    (fun _ hj => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj) hfinite hvanish z hz

end LeanCanny.Algebra.FiniteFiberLowestCoefficient
