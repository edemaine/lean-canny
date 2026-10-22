/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRegularJacobianBudget
public import LeanCanny.ETR.TubeCoordinateAnnihilatorRegular
public import LeanCanny.ETR.TubeNativeSampleGeometry
public import LeanCanny.Geometry.PolynomialCalculus
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! # The native regular Jacobian controls the compiled affine chart -/

@[expose] public section
namespace LeanCanny.ETR.TubeRegularJacobianChart
open LeanCanny.Encoding LeanCanny.Algebra Geometry
open TubeEncoding TubeProjectionEncoding
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

noncomputable def coordinateEquiv (bits : List Bool) :
    TubeRegularSource.Index bits ≃ Option (TubeSource.Coordinate bits) :=
  Equiv.optionCongr (Equiv.optionSubtypeNe (TubePolynomial.base _))

noncomputable def variation (bits : List Bool) :
    (TubeRegularSource.Index bits → ℝ) →L[ℝ] (TubeRegularSource.Variable bits → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h i => i.elim (h ((coordinateEquiv bits).symm none))
        (fun k => k.elim (fun j => j.elim (fun p => h ((coordinateEquiv bits).symm (some p)))
          (fun _ => 0)) (fun _ => 0))
      map_add' := by intro a b; funext i; rcases i with _ | ((i | i) | p) <;> simp
      map_smul' := by intro a b; funext i; rcases i with _ | ((i | i) | p) <;> simp }

noncomputable def assignment (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* ℝ)
    (h : TubeRegularSource.Index bits → ℝ) : TubeRegularSource.Variable bits → ℝ :=
  fun i => i.elim (h ((coordinateEquiv bits).symm none))
    (TubeMacaulay.values _ φ (fun p => h ((coordinateEquiv bits).symm (some p))))

lemma assignment_add (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* ℝ)
    (x h : TubeRegularSource.Index bits → ℝ) :
    assignment bits φ (x + h) = assignment bits φ x + variation bits h := by
  funext i
  rcases i with _ | ((i | i) | p) <;> simp [assignment, variation, TubeMacaulay.values]

lemma assignment_hasFDerivAt (bits : List Bool)
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* ℝ)
    (x : TubeRegularSource.Index bits → ℝ) :
    HasFDerivAt (assignment bits φ) (variation bits) x := by
  have he : assignment bits φ = fun h => assignment bits φ 0 + variation bits h := by
    funext h
    simpa only [zero_add] using assignment_add bits φ 0 h
  rw [he]
  simpa only [zero_add, Pi.add_apply] using
    (hasFDerivAt_const (assignment bits φ 0) x).fun_add (variation bits).hasFDerivAt

lemma derivative_variation (bits : List Bool)
    (p : MvPolynomial (TubeRegularSource.Variable bits) ℤ)
    (z : TubeRegularSource.Variable bits → ℝ) (h : TubeRegularSource.Index bits → ℝ) :
    PolynomialCalculus.derivative (Int.castRingHom ℝ) p z (variation bits h) =
      ∑ j, (MvPolynomial.pderiv (TubeRegularJacobianBudget.coordinate bits j) p).eval₂
        (Int.castRingHom ℝ) z * h j := by
  rw [PolynomialCalculus.derivative_apply]
  have he := (coordinateEquiv bits).sum_comp
    (fun j => (MvPolynomial.pderiv (j.elim none (fun i => some (.inl (.inl i)))) p).eval₂
      (Int.castRingHom ℝ) z * h ((coordinateEquiv bits).symm j))
  calc
    _ = ∑ j : Option (TubeSource.Coordinate bits),
      (MvPolynomial.pderiv (j.elim none (fun i => some (.inl (.inl i)))) p).eval₂
        (Int.castRingHom ℝ) z * h ((coordinateEquiv bits).symm j) := by
      simp [variation, Fintype.sum_option, Fintype.sum_sum_type]
    _ = _ := he.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Equiv.symm_apply_apply]
      congr 2
      cases j <;> rfl

noncomputable def nativeDerivative (bits : List Bool)
    (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* ℝ)
    (x : TubeRegularSource.Index bits → ℝ) :
    (TubeRegularSource.Index bits → ℝ) →L[ℝ] (TubeRegularSource.Index bits → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    (PolynomialCalculus.derivative (Int.castRingHom ℝ)
      (TubeRegularSource.polynomial bits s j) (assignment bits φ x)).comp (variation bits)

lemma native_hasFDerivAt (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* ℝ)
    (x : TubeRegularSource.Index bits → ℝ) :
    HasFDerivAt (fun y j => (TubeRegularSource.polynomial bits s j).eval₂
      (Int.castRingHom ℝ) (assignment bits φ y)) (nativeDerivative bits s φ x) x := by
  apply hasFDerivAt_pi.mpr
  intro j
  exact (PolynomialCalculus.hasFDerivAt (Int.castRingHom ℝ)
    (TubeRegularSource.polynomial bits s j) (assignment bits φ x)).comp x
      (assignment_hasFDerivAt bits φ x)

lemma nativeDerivative_injective (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (φ : TubeMacaulay.Coefficients (CompactSource.term bits).arity →+* ℝ)
    (x : TubeRegularSource.Index bits → ℝ)
    (hdet : (TubeRegularJacobianBudget.polynomial bits s).eval₂
      (Int.castRingHom ℝ) (assignment bits φ x) ≠ 0) :
    Function.Injective (nativeDerivative bits s φ x) := by
  rw [TubeRegularJacobianBudget.eval_polynomial] at hdet
  have hi := Matrix.mulVec_injective_of_det_ne_zero hdet
  intro a b hab
  apply hi
  funext j
  have H := congrFun hab j
  simpa only [nativeDerivative, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    derivative_variation, Matrix.mulVec, dotProduct] using H


noncomputable def chartSpatial (bits : List Bool) :
    TubeCharacteristicQuotient.RegularChart bits ℝ →L[ℝ] (TubeRegularSource.Index bits → ℝ) :=
  ContinuousLinearMap.pi fun j =>
    (ContinuousLinearMap.proj (TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits)
      (coordinateEquiv bits j))).comp (ContinuousLinearMap.snd ℝ ℝ _)

noncomputable def headLinear (bits : List Bool) (ell : ℕ → ℤ) :
    TubeCharacteristicQuotient.RegularChart bits ℝ →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ _ - ∑ i, (ell (i.val + 1) : ℝ) •
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ ℝ _)

section Chart
open TubeCharacteristicQuotient
variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)
  (epsilon : ℝ)
  (hd : ∀ i, i < TubeParameter.parameterCount (source c) →
    (d c i).eval₂ (Int.castRingHom ℝ) epsilon ≠ 0)

include hd in
lemma selected_row (a : RegularChart (source c) ℝ) (j : TubeRegularSource.Index (source c)) :
    regularSystem source active n d ell c epsilon a
      (TubeCompiledAffineRoots.regularRowIndex (source c) j) =
    TubeCleared.scale (source c) (d c) (Int.castRingHom ℝ) epsilon *
      (TubeRegularSource.polynomial (source c)
        (activeSet (TubeIndexed.arity (source c)) (active c)) j).eval₂ (Int.castRingHom ℝ)
        (assignment (source c)
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom ℝ) epsilon)
          (chartSpatial (source c) a)) := by
  rw [show regularSystem source active n d ell c epsilon a
    (TubeCompiledAffineRoots.regularRowIndex (source c) j) = _ from
    TubeCompiledAffineRoots.eval_selected_row source active n d ell c epsilon a.1 a.2 hd j]
  have hv : (fun i => (Fin.cons (1 : ℝ) a.2 :
      Fin (TubeParameter.spatialCount (source c)) → ℝ) (TubeParameter.spatialEquiv (source c) i)) =
      (fun i => i.elim 1 (fun k => a.2 (TubeMacaulay.coordinateEquiv (TubeIndexed.arity (source c)) k))) := by
    funext i
    cases i <;> rfl
  rw [hv, TubeRegularMacaulay.spatial_eval_chart]
  congr 2
  funext i
  rcases i with _ | ((i | i) | p) <;>
    simp [assignment, chartSpatial, TubeMacaulay.values]

lemma regularSystem_hasFDerivAt (a : RegularChart (source c) ℝ) :
    HasFDerivAt (regularSystem source active n d ell c epsilon)
      (fderiv ℝ (regularSystem source active n d ell c epsilon) a) a := by
  have h : ContDiff ℝ 1 (regularSystem source active n d ell c epsilon) := by
    apply contDiff_pi.mpr
    intro i
    exact ParametricPolynomialCalculus.mvPolynomial_eval₂ _ _ _ 1
      (regularCoefficientMap_contDiff (source c) epsilon) (regularChart_contDiff (source c))
  exact (h.differentiable (by simp)).differentiableAt.hasFDerivAt

include hd in
lemma selected_derivative (a h : RegularChart (source c) ℝ)
    (j : TubeRegularSource.Index (source c)) :
    fderiv ℝ (regularSystem source active n d ell c epsilon) a h
      (TubeCompiledAffineRoots.regularRowIndex (source c) j) =
    TubeCleared.scale (source c) (d c) (Int.castRingHom ℝ) epsilon *
      nativeDerivative (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
        (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom ℝ) epsilon)
        (chartSpatial (source c) a) (chartSpatial (source c) h) j := by
  have hr := (hasFDerivAt_apply (𝕜 := ℝ)
    (TubeCompiledAffineRoots.regularRowIndex (source c) j) _).comp a
      (regularSystem_hasFDerivAt source active n d ell c epsilon a)
  have hn := (native_hasFDerivAt (source c)
    (activeSet (TubeIndexed.arity (source c)) (active c))
    (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom ℝ) epsilon)
    (chartSpatial (source c) a)).comp a (chartSpatial (source c)).hasFDerivAt
  have hj := ((hasFDerivAt_apply (𝕜 := ℝ) j _).comp a hn).const_mul
    (TubeCleared.scale (source c) (d c) (Int.castRingHom ℝ) epsilon)
  have he : (fun a => regularSystem source active n d ell c epsilon a
      (TubeCompiledAffineRoots.regularRowIndex (source c) j)) = _ :=
    funext fun a => selected_row source active n d ell c epsilon hd a j
  simp only [Function.comp_def] at hr hj
  rw [← he] at hj
  exact congrArg (fun D => D h) (hr.unique hj)

lemma head_derivative (a h : RegularChart (source c) ℝ) :
    fderiv ℝ (regularSystem source active n d ell c epsilon) a h
      (finiteParameterIndex (source c)) = headLinear (source c) (ell c) h := by
  have hr := (hasFDerivAt_apply (𝕜 := ℝ) (finiteParameterIndex (source c)) _).comp a
    (regularSystem_hasFDerivAt source active n d ell c epsilon a)
  have he : (fun a => regularSystem source active n d ell c epsilon a
    (finiteParameterIndex (source c))) = headLinear (source c) (ell c) := by
    funext b
    rw [regularSystem_head]
    simp [headLinear, projectionForm]
  simp only [Function.comp_def] at hr
  rw [he] at hr
  exact congrArg (fun D => D h) (hr.unique (headLinear (source c) (ell c)).hasFDerivAt)


include hd in
/-- Nonvanishing of the native singularity polynomial gives the actual analytic
Jacobian hypothesis used by simple-root persistence. No root or fiber-finiteness
hypothesis is required. -/
theorem regularSystem_isInvertible (a : RegularChart (source c) ℝ)
    (hdet : (TubeRegularJacobianBudget.polynomial (source c)
      (activeSet (TubeIndexed.arity (source c)) (active c))).eval₂ (Int.castRingHom ℝ)
        (assignment (source c)
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom ℝ) epsilon)
          (chartSpatial (source c) a)) ≠ 0) :
    (fderiv ℝ (regularSystem source active n d ell c epsilon) a).IsInvertible := by
  let D := fderiv ℝ (regularSystem source active n d ell c epsilon) a
  have hi : Function.Injective D := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro h hh
    have hs : chartSpatial (source c) h = 0 := by
      apply nativeDerivative_injective (source c)
        (activeSet (TubeIndexed.arity (source c)) (active c))
        (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom ℝ) epsilon)
        (chartSpatial (source c) a) hdet
      rw [map_zero]
      funext j
      have H := congrFun hh (TubeCompiledAffineRoots.regularRowIndex (source c) j)
      change D h (TubeCompiledAffineRoots.regularRowIndex (source c) j) = 0 at H
      rw [show D h (TubeCompiledAffineRoots.regularRowIndex (source c) j) = _ from
        selected_derivative source active n d ell c epsilon hd a h j] at H
      exact (mul_eq_zero.mp H).resolve_left (TubeCompiledAffineRoots.scale_ne_zero _ _ _ hd)
    have hy : h.2 = 0 := by
      funext i
      obtain ⟨k, rfl⟩ := ((coordinateEquiv (source c)).trans
        (TubeMacaulay.coordinateEquiv (TubeIndexed.arity (source c)))).surjective i
      exact congrFun hs k
    have H := congrFun hh (finiteParameterIndex (source c))
    change D h (finiteParameterIndex (source c)) = 0 at H
    rw [show D h (finiteParameterIndex (source c)) = _ from
      head_derivative source active n d ell c epsilon a h] at H
    have hu : h.1 = 0 := by simpa [headLinear, hy] using H
    exact Prod.ext hu hy
  have hdim : Module.finrank ℝ (RegularChart (source c) ℝ) =
      Module.finrank ℝ (Fin (TubeParameter.spatialCount (source c)) → ℝ) := by
    simp [RegularChart, Module.finrank_prod, TubeParameter.spatialCount, Nat.add_comm]
  refine ⟨(LinearEquiv.ofInjectiveOfFinrankEq D.toLinearMap hi hdim).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.coe_injective
  change (LinearEquiv.ofInjectiveOfFinrankEq D.toLinearMap hi hdim).toLinearMap = D.toLinearMap
  exact LinearEquiv.coe_ofInjectiveOfFinrankEq D.toLinearMap hi hdim

end Chart

/-- The packet instance uses precisely the native assignment formed by fixing
its stored direction and rational parameters. -/
theorem packet_isInvertible (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hdet : (TubeRegularJacobianBudget.polynomial (pairFst c)
      (activeSet (TubeIndexed.arity (pairFst c)) mask)).eval₂ (Int.castRingHom ℝ)
        (TubeNativeSampleGeometry.extend c alpha
          (TubeCompiledAffineRoots.decodedPoint (pairFst c) z)) ≠ 0) :
    (fderiv ℝ (TubeCharacteristicQuotient.regularSystem pairFst (fun _ => mask)
      TubeLevelPacket.numerator TubeLevelPacket.denominator (fun _ => ell) c alpha)
        (TubeLevelPacket.projectionValue c z, fun j => z j.succ)).IsInvertible := by
  apply regularSystem_isInvertible pairFst (fun _ => mask)
    TubeLevelPacket.numerator TubeLevelPacket.denominator (fun _ => ell) c alpha
    (fun i _ => TubeLevelPacket.denominator_eval_ne_zero c i alpha)
  convert hdet using 1
  congr 2
  funext i
  rcases i with _ | ((i | i) | p) <;>
    simp [assignment, chartSpatial, TubeNativeSampleGeometry.extend,
      TubeCompiledAffineRoots.decodedPoint, TubeMacaulay.values, TubeLevelPacket.parameters]

end LeanCanny.ETR.TubeRegularJacobianChart
