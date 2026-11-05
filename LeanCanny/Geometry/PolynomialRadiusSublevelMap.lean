/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.TwoCircleSublevelMap
public import LeanCanny.Geometry.GeneralCriticalValueBounds
public import LeanCanny.Geometry.SquaredDistanceProper
public import LeanCanny.Geometry.ProjectionCritical
/-! # Actual norm-boundary critical equations control a proper regular map

The singular equation is replaced by a small positive squared-residual level.
Two circle slacks retain its sublevel and the original Euclidean radius.
The only remaining criticality equations are the literal Lagrange equations
used by the constructed parameterized boundary Gram determinant.
-/
@[expose] public section
namespace LeanCanny.Geometry.PolynomialRadiusSublevelMap
open LeanCanny.Algebra MvPolynomial Set
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def normPolynomial (n : ℕ) : MvPolynomial (Fin n) ℤ := ∑ i, X i ^ 2
noncomputable def normValue (x : Fin n → ℝ) : ℝ := (normPolynomial n).eval₂ (Int.castRingHom ℝ) x
noncomputable def residual (q : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) :=
  (q ^ 2).eval₂ (Int.castRingHom ℝ) x

theorem normValue_eq_sum (x : Fin n → ℝ) : normValue x = ∑ i, x i ^ 2 := by
  simp only [normValue,normPolynomial,eval₂_sum,eval₂_pow,eval₂_X]
theorem normValue_eq_distance (x : Fin n → ℝ) : normValue x = SquaredDistanceFibers.value 0 x := by
  simp only [normValue_eq_sum,SquaredDistanceFibers.value,Pi.zero_apply,sub_zero]
theorem residual_eq (q : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) :
    residual q x = (q.eval₂ (Int.castRingHom ℝ) x) ^ 2 := by simp only [residual,eval₂_pow]

theorem norm_single (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ normValue x (Pi.single i 1) = 2 * x i := by
  unfold normValue
  rw [PolynomialCalculus.fderiv_eq,PolynomialCalculus.derivative_single]
  simp [normPolynomial,pderiv_X,Pi.single_apply]

theorem residual_single (q : MvPolynomial (Fin n) ℤ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (residual q) x (Pi.single i 1) =
      2 * q.eval₂ (Int.castRingHom ℝ) x * (pderiv i q).eval₂ (Int.castRingHom ℝ) x := by
  unfold residual
  rw [PolynomialCalculus.fderiv_eq,PolynomialCalculus.derivative_single]
  rw [pow_two,pderiv_mul,eval₂_add,eval₂_mul,eval₂_mul]
  ring

noncomputable def map (q : MvPolynomial (Fin n) ℤ) := TwoCircleSublevelMap.energy (residual q) normValue

theorem smooth (q : MvPolynomial (Fin n) ℤ) : ContDiff ℝ 1 (map q) :=
  TwoCircleSublevelMap.contDiff_energy (residual q) normValue
    ((ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (q^2)).of_le le_top)
    ((ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (normPolynomial n)).of_le le_top)

theorem proper (q : MvPolynomial (Fin n) ℤ) : IsProperMap (map q) := by
  apply TwoCircleSublevelMap.proper_energy (residual q) normValue
    (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (q^2)).continuous
    (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (normPolynomial n)).continuous
  · intro x
    rw [residual_eq]
    exact sq_nonneg _
  · intro x
    rw [normValue_eq_sum]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · intro r
    by_cases hr : 0 ≤ r
    · simpa only [normValue_eq_distance] using SquaredDistanceFibers.compact_sublevel (0 : Fin n → ℝ) r hr
    · have HE : {x : Fin n → ℝ | normValue x ≤ r} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have HN := SquaredDistanceFibers.nonneg (0 : Fin n → ℝ) x
        rw [←normValue_eq_distance] at HN
        exact hr (HN.trans hx)
      rw [HE]
      exact isCompact_empty

theorem regular (q : MvPolynomial (Fin n) ℤ) (e r : ℝ) (hr : 0 < r)
    (he : ∀ x : Fin n → ℝ, residual q x = e → Function.Surjective (fderiv ℝ (residual q) x))
    (hboundary : ∀ (x : Fin n → ℝ) (lambda : ℝ), residual q x = e → normValue x = r →
      ¬ ∀ i, 2 * x i + lambda * (2 * q.eval₂ (Int.castRingHom ℝ) x *
        (pderiv i q).eval₂ (Int.castRingHom ℝ) x) = 0)
    (p : (Fin n → ℝ) × (ℂ × ℂ)) (hp : map q p = (e,r)) :
    Function.Surjective (fderiv ℝ (map q) p) := by
  have HG := (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (q^2)).differentiable (by simp)
  have HH := (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (normPolynomial n)).differentiable (by simp)
  have H1 : residual q p.1 + Complex.normSq p.2.1 = e := congrArg Prod.fst hp
  have H2 : normValue p.1 + Complex.normSq p.2.2 = r := congrArg Prod.snd hp
  have HF := CircleSublevelLift.regular_energy (residual q) HG e he (p.1,p.2.1) H1
  rw [(CircleSublevelLift.hasFDerivAt_energy (residual q) (p.1,p.2.1) (HG p.1)).fderiv] at HF
  change Function.Surjective (fderiv ℝ (TwoCircleSublevelMap.energy (residual q) normValue) p)
  rw [(TwoCircleSublevelMap.hasFDerivAt_energy (residual q) normValue p (HG p.1) (HH p.1)).fderiv]
  apply TwoCircleSublevelMap.derivative_surjective
    (fderiv ℝ (residual q) p.1) (fderiv ℝ normValue p.1) p.2.1 p.2.2 HF
  · intro hw Hz
    have HX : p.1 = 0 := by
      funext i
      have H := congrArg (fun D : (Fin n → ℝ) →L[ℝ] ℝ => D (Pi.single i 1)) Hz
      rw [norm_single,zero_apply] at H
      change p.1 i = 0
      linarith
    have H : (0 : ℝ) = r := by simpa [hw,HX,normValue_eq_sum] using H2
    exact (ne_of_gt hr) H.symm
  · intro hz hw c HD
    have HE : residual q p.1 = e := by
      rw [hz] at H1
      simpa using H1
    have HR : normValue p.1 = r := by
      rw [hw] at H2
      simpa using H2
    apply hboundary p.1 (-c) HE HR
    intro i
    have H := congrArg (fun D : (Fin n → ℝ) →L[ℝ] ℝ => D (Pi.single i 1)) HD
    rw [norm_single,smul_apply,smul_eq_mul,residual_single] at H
    nlinarith

theorem small_regular (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (e : ℝ) (he : 0 < e)
    (hsmall : e ≤ GeneralCriticalValueBounds.level n (2*D+1) (2*b))
    (x : Fin n → ℝ) (hx : residual q x = e) :
    Function.Surjective (fderiv ℝ (residual q) x) := by
  apply GeneralCriticalValueBounds.regular_interval (q^2) (2*D+1) (2*b) ?_ (by omega) ?_ e he hsmall x hx
  · exact ((totalDegree_pow q 2).trans (Nat.mul_le_mul_left 2 hD)).trans (by omega)
  · apply (MvMass.pow_le q 2).trans
    simpa only [←pow_mul,Nat.mul_comm b 2] using Nat.pow_le_pow_left hb 2

end LeanCanny.Geometry.PolynomialRadiusSublevelMap
