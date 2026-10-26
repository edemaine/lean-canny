/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.LinearProjectionSystem
public import LeanCanny.Geometry.AffineCoordinateEliminant

/-! # Bounded equations for linear projections of regular affine roots

The concrete Macaulay numerator annihilates every weighted projection of a
regular root. Its degree bound does not depend on the weight values.
-/

@[expose] public section
namespace LeanCanny.Geometry.LinearProjectionEliminant
open MvPolynomial LeanCanny.Algebra LinearProjectionSystem
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def polynomial (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) (W : ℕ) : Polynomial R :=
  MacaulayLowestBounds.polynomial (rows q d v) (AffineCoordinateSystem.degrees d) W

theorem ne_zero [IsDomain R] (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) (W : ℕ) : polynomial q d v W ≠ 0 := MacaulayLowestBounds.ne_zero _ _ _

theorem degree_le (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (v : Fin n → R) (W : ℕ) :
    (polynomial q d v W).natDegree ≤ FixedWidthPolynomial.count (n + 1) W := by
  simpa only [polynomial, Nat.mul_one] using
    MacaulayLowestBounds.degree_le (rows q d v) (AffineCoordinateSystem.degrees d) W 1
      (coefficient_degree q d v)

omit [CommRing R] in
theorem coefficient_size_le (q : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (v : Fin n → ℤ) (W B b w : ℕ)
    (hq : ∀ j e, ((q j).coeff e).natAbs ≤ 2 ^ b) (hv : ∀ i, (v i).natAbs ≤ 2 ^ w)
    (hB : 2 ^ b + 1 + n * 2 ^ w ≤ 2 ^ B) (k : ℕ) :
    ((polynomial q d v W).coeff k).natAbs.size ≤
      (FixedWidthPolynomial.count (n + 1) W).size * FixedWidthPolynomial.count (n + 1) W +
        FixedWidthPolynomial.count (n + 1) W * (B + 1) + 1 := by
  exact MacaulayLowestBounds.coefficient_size_le (rows q d v) (AffineCoordinateSystem.degrees d) W B
    (fun j e => (coefficient_mass q d v b w hq hv j e).trans hB) k

noncomputable def linear (φ : R →+* ℝ) (v : Fin n → R) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, φ (v i) • ContinuousLinearMap.proj i

theorem linear_apply (φ : R →+* ℝ) (v : Fin n → R) (x : Fin n → ℝ) :
    linear φ v x = ∑ i, φ (v i) * x i := by
  simp [linear]

omit [CommRing R] in
/-- Adding the retained linear projection gives a triangular Jacobian. -/
theorem augment_isInvertible (f : (Fin n → ℝ) → Fin n → ℝ) (l : (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ) (hf : DifferentiableAt ℝ f x) (hJac : (fderiv ℝ f x).IsInvertible) :
    (fderiv ℝ (fun a : ℝ × (Fin n → ℝ) => (Fin.cons (a.1 - l a.2) (f a.2) : Fin (n + 1) → ℝ))
      (l x, x)).IsInvertible := by
  let a := (l x, x)
  let D : (ℝ × (Fin n → ℝ)) →L[ℝ] (Fin (n + 1) → ℝ) := ContinuousLinearMap.pi
    (Fin.cons (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ) -
      l.comp (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))
      (fun j => (ContinuousLinearMap.proj j).comp ((fderiv ℝ f x).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)))))
  have hfst : HasFDerivAt (Prod.fst : ℝ × (Fin n → ℝ) → ℝ)
      (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ)) a := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : ℝ × (Fin n → ℝ) → Fin n → ℝ)
      (ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) a := hasFDerivAt_snd
  have hder : HasFDerivAt (fun a : ℝ × (Fin n → ℝ) =>
      (Fin.cons (a.1 - l a.2) (f a.2) : Fin (n + 1) → ℝ)) D a := by
    apply hasFDerivAt_pi.mpr
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · exact hfst.sub (l.hasFDerivAt.comp a hsnd)
    · exact ((hasFDerivAt_apply (𝕜 := ℝ) j (f x)).comp x hf.hasFDerivAt).comp a hsnd
  rw [hder.fderiv]
  have hinj : Function.Injective D := by
    intro u v huv
    have htail : fderiv ℝ f x u.2 = fderiv ℝ f x v.2 := by
      funext j
      exact congrFun huv j.succ
    have hsp := hJac.injective htail
    have hhead := congrFun huv 0
    change u.1 - l u.2 = v.1 - l v.2 at hhead
    rw [hsp] at hhead
    exact Prod.ext (sub_left_inj.mp hhead) hsp
  have hdim : Module.finrank ℝ (ℝ × (Fin n → ℝ)) = Module.finrank ℝ (Fin (n + 1) → ℝ) := by
    simp [Module.finrank_prod, Nat.add_comm]
  refine ⟨(LinearEquiv.ofInjectiveOfFinrankEq D.toLinearMap hinj hdim).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.coe_injective
  exact LinearEquiv.coe_ofInjectiveOfFinrankEq _ hinj hdim

theorem eval_eq_zero [IsDomain R] (φ : R →+* ℝ)
    (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (v : Fin n → R) (W : ℕ)
    (hW : Macaulay.level (AffineCoordinateSystem.degrees d) < 2 ^ W) (x : Fin n → ℝ)
    (hroot : ∀ j, (q j).eval₂ φ x = 0)
    (hJac : (fderiv ℝ (fun y => fun j => (q j).eval₂ φ y) x).IsInvertible) :
    (polynomial q d v W).eval₂ φ (∑ i, φ (v i) * x i) = 0 := by
  let f := fun y : Fin n → ℝ => fun j => (q j).eval₂ φ y
  let l := linear φ v
  have hf : ContDiff ℝ 1 f := contDiff_pi.mpr
    (fun j => (ProjectionCritical.contDiff_eval φ (q j)).of_le le_top)
  have hfamily : MacaulayRegularPersistence.family (rows q d v)
      (AffineCoordinateEliminant.coefficientMap φ) AffineCoordinateEliminant.chart =
      (fun a : ℝ × (Fin n → ℝ) => Fin.cons (a.1 - l a.2) (f a.2)) := by
    funext a
    change (fun j => (rows q d v j).eval₂ (Polynomial.eval₂RingHom φ a.1)
      (fun k => (AffineCoordinateSystem.layout.symm k).elim 1 a.2)) =
        Fin.cons (a.1 - l a.2) (f a.2)
    rw [eval_rows φ q d hD v a.1 a.2, show l a.2 = ∑ i, φ (v i) * a.2 i from linear_apply φ v a.2]
  have he := MacaulayRegularPersistence.numerator_trailingCoeff_eq_zero_of_regular_root
    (rows q d v) (AffineCoordinateSystem.degrees d) W
    (MacaulayUniversal.degree_lt_width _ _ (AffineCoordinateSystem.degrees_pos d hd) hW) hW
    (homogeneous q d v) (AffineCoordinateSystem.degrees_pos d hd)
    (AffineCoordinateEliminant.coefficientMap φ) AffineCoordinateEliminant.chart
    (AffineCoordinateEliminant.coefficientMap_contDiff φ) AffineCoordinateEliminant.chart_contDiff
    AffineCoordinateEliminant.chart_nonzero (l x, x)
    (by rw [hfamily]; ext j; refine Fin.cases (by simp) (fun j => hroot j) j)
    (by rw [hfamily]; exact augment_isInvertible f l x (hf.contDiffAt.differentiableAt one_ne_zero) hJac)
  change (AffineCoordinateEliminant.coefficientMap φ (l x, x))
    (MacaulayLowestBounds.polynomial (rows q d v) (AffineCoordinateSystem.degrees d) W) = 0 at he
  change (polynomial q d v W).eval₂ φ (l x) = 0 at he
  simpa only [l, linear_apply] using he

end LeanCanny.Geometry.LinearProjectionEliminant
