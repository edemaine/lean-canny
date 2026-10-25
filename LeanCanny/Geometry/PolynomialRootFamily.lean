/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootProjection
public import LeanCanny.Geometry.PolynomialCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # Analytic regularity of explicit parameterized polynomial systems

The parameter is in the coefficient ring `ℝ[X]`; the multivariate unknowns
remain separate. Evaluation is smooth in both, and its derivative in the
unknowns is invertible exactly when the evaluated formal Jacobian determinant
is nonzero. Thus regular root arcs can be constructed directly from polynomial
systems, rather than requiring a separately supplied analytic model.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialRootFamily
open MvPolynomial Set
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

noncomputable def value (q : ι → MvPolynomial ι (Polynomial ℝ))
    (z : ℝ × (ι → ℝ)) : ι → ℝ :=
  fun i => (q i).eval₂ (Polynomial.evalRingHom z.1) z.2

theorem contDiff_eval (p : MvPolynomial ι (Polynomial ℝ)) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun z : ℝ × (ι → ℝ) => p.eval₂ (Polynomial.evalRingHom z.1) z.2) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    have hc : ContDiff ℝ n (fun t : ℝ => c.eval t) := by
      induction c using Polynomial.induction_on' with
      | add p q hp hq => simpa only [Polynomial.eval_add] using hp.add hq
      | monomial k r =>
        simpa only [Polynomial.eval_monomial, id_eq] using contDiff_const.mul (contDiff_id.pow k)
    simpa only [eval₂_C, Polynomial.coe_evalRingHom, Function.comp_def] using hc.comp contDiff_fst
  | add p q hp hq => simpa only [eval₂_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [eval₂_mul, eval₂_X, Function.comp_def] using
      hp.mul ((contDiff_apply ℝ (fun _ : ι => ℝ) i).comp contDiff_snd)

theorem contDiff_value (q : ι → MvPolynomial ι (Polynomial ℝ)) (n : WithTop ℕ∞) :
    ContDiff ℝ n (value q) := contDiff_pi.mpr (fun i => contDiff_eval (q i) n)

noncomputable def derivative (q : ι → MvPolynomial ι (Polynomial ℝ))
    (z : ℝ × (ι → ℝ)) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    PolynomialCalculus.derivative (Polynomial.evalRingHom z.1) (q i) z.2

theorem fderiv_comp_inr (q : ι → MvPolynomial ι (Polynomial ℝ)) (z : ℝ × (ι → ℝ)) :
    fderiv ℝ (value q) z ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ) = derivative q z := by
  have hpair : HasFDerivAt (fun x : ι → ℝ => (z.1, x))
      (ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)) z.2 := by
    convert (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2) using 1
    <;> rfl
  have hd : HasFDerivAt (fun x => value q (z.1, x)) (derivative q z) z.2 := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact PolynomialCalculus.hasFDerivAt (Polynomial.evalRingHom z.1) (q i) z.2
  exact (((contDiff_value q 1).contDiffAt.differentiableAt one_ne_zero).hasFDerivAt.comp z.2 hpair).unique hd

variable [DecidableEq ι]

noncomputable def jacobian (q : ι → MvPolynomial ι (Polynomial ℝ)) :
    MvPolynomial ι (Polynomial ℝ) := Matrix.det (fun i j => pderiv j (q i))

theorem eval_jacobian (q : ι → MvPolynomial ι (Polynomial ℝ)) (z : ℝ × (ι → ℝ)) :
    (jacobian q).eval₂ (Polynomial.evalRingHom z.1) z.2 =
      Matrix.det (fun i j => (pderiv j (q i)).eval₂ (Polynomial.evalRingHom z.1) z.2) :=
  (MvPolynomial.eval₂Hom (Polynomial.evalRingHom z.1) z.2).map_det _

omit [DecidableEq ι] in
theorem derivative_apply (q : ι → MvPolynomial ι (Polynomial ℝ))
    (z : ℝ × (ι → ℝ)) (h : ι → ℝ) :
    derivative q z h =
      Matrix.mulVec (fun i j => (pderiv j (q i)).eval₂ (Polynomial.evalRingHom z.1) z.2) h := by
  funext i
  exact PolynomialCalculus.derivative_apply _ _ _ _

/-- The determinant is the actual analytic simplicity criterion, in both
directions and also in dimension zero. -/
theorem isInvertible_iff (q : ι → MvPolynomial ι (Polynomial ℝ)) (z : ℝ × (ι → ℝ)) :
    (fderiv ℝ (value q) z ∘L ContinuousLinearMap.inr ℝ ℝ (ι → ℝ)).IsInvertible ↔
      (jacobian q).eval₂ (Polynomial.evalRingHom z.1) z.2 ≠ 0 := by
  rw [fderiv_comp_inr, eval_jacobian]
  let M : Matrix ι ι ℝ :=
    fun i j => (pderiv j (q i)).eval₂ (Polynomial.evalRingHom z.1) z.2
  have hD : ∀ h, derivative q z h = M.mulVec h := derivative_apply q z
  constructor
  · intro h
    apply IsUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det M).mp
    apply Matrix.mulVec_injective_iff_isUnit.mp
    intro a b hab
    apply h.injective
    simpa only [hD] using hab
  · intro hdet
    have hinj : Function.Injective (derivative q z) := by
      intro a b hab
      apply Matrix.mulVec_injective_of_det_ne_zero hdet
      simpa only [hD] using hab
    refine ⟨(LinearEquiv.ofInjectiveOfFinrankEq (derivative q z).toLinearMap hinj rfl).toContinuousLinearEquiv, ?_⟩
    apply ContinuousLinearMap.coe_injective
    exact LinearEquiv.coe_ofInjectiveOfFinrankEq _ hinj rfl

omit [DecidableEq ι] in
/-- A compact bound on the unknowns proves properness for the actual polynomial
system. No enumeration or compactness of the parameter line is assumed. -/
theorem isProperMap_of_compact_bound (q : ι → MvPolynomial ι (Polynomial ℝ))
    {K : Set (ι → ℝ)} (hK : IsCompact K)
    (hbound : ∀ t x, value q (t, x) = 0 → x ∈ K) :
    IsProperMap (RootProjection.projection (value q)) :=
  RootProjection.isProperMap_of_compact_bound _ (contDiff_value q 1).continuous hK
    (fun z => hbound z.val.1 z.val.2 z.property)

omit [DecidableEq ι] in
/-- A proper level polynomial suffices even when the roots have no fixed
compact bound as the level varies over the whole parameter line. -/
theorem isProperMap_of_level (q : ι → MvPolynomial ι (Polynomial ℝ))
    {g : (ι → ℝ) → ℝ} (hg : IsProperMap g)
    (hlevel : ∀ t x, value q (t, x) = 0 → t = g x) :
    IsProperMap (RootProjection.projection (value q)) :=
  ProperProjection.isProperMap_fst_of_level
    (isClosed_eq (contDiff_value q 1).continuous continuous_const) hg
    (fun z hz => hlevel z.1 z.2 hz)

end LeanCanny.Geometry.PolynomialRootFamily
