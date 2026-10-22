/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilator
public import LeanCanny.ETR.TubeCharacteristicRoots
public import LeanCanny.ETR.TubeCoordinateAnnihilatorDyadic

/-! # Coordinate annihilation at simple compiled roots

An invertible derivative of the actual compiled chart equations gives a
characteristic-shifted root curve. Replacing only its projection coordinate
transports this curve to every coordinate projection. No finite-fiber
hypothesis or supplied persistence certificate is used.
-/

@[expose] public section
namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.Geometry
open Filter
open scoped Topology Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

variable (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
  (ell ell' : List Bool → ℕ → ℤ) (c : List Bool)

noncomputable def projectionForm (l : ℕ → ℤ) (y : Fin (TubeProjectionEncoding.pointCount (TubeIndexed.arity (source c)) + 1) → ℝ) : ℝ :=
  ∑ i, (l (i.val + 1) : ℝ) * y i

theorem regularSystem_head (epsilon : ℝ) (a : RegularChart (source c) ℝ) :
    regularSystem source active n d ell c epsilon a (finiteParameterIndex (source c)) =
      a.1 - projectionForm source c (ell c) a.2 :=
  TubeCompiledAffineRoots.eval_projection_row source active n d ell c epsilon a.1 a.2

theorem regularSystem_tail_eq (epsilon : ℝ) (a b : RegularChart (source c) ℝ) (hab : a.2 = b.2)
    (i : Fin (TubeParameter.spatialCount (source c))) (hi : i.val ≠ 0) :
    regularSystem source active n d ell c epsilon a i = regularSystem source active n d ell' c epsilon b i := by
  change MvPolynomial.eval₂ (regularCoefficientMap epsilon a.1) (regularChart (source c) a)
      (TubeBivariate.rows source active n d ell c i) =
    MvPolynomial.eval₂ (regularCoefficientMap epsilon b.1) (regularChart (source c) b)
      (TubeBivariate.rows source active n d ell' c i)
  simp only [TubeBivariate.rows, hi, ite_false, MvPolynomial.eval₂_map]
  have hc (u : ℝ) : (regularCoefficientMap epsilon u).comp Polynomial.C =
      Polynomial.eval₂RingHom (Int.castRingHom ℝ) epsilon := by
    ext <;> simp only [regularCoefficientMap, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [hc a.1, hc b.1]
  have hz : regularChart (source c) a = regularChart (source c) b := by
    unfold regularChart
    rw [hab]
  rw [hz]

/-- A simple root for one projection supplies lowest-coefficient vanishing
for every other projection by transporting its actual shifted root curve. -/
theorem trailingCoeff_eq_zero_of_regular_reprojection (epsilon : ℝ) (a : RegularChart (source c) ℝ)
    (hroot : regularSystem source active n d ell c epsilon a = 0)
    (hJac : (fderiv ℝ (regularSystem source active n d ell c epsilon) a).IsInvertible) :
    regularCoefficientMap epsilon (projectionForm source c (ell' c) a.2)
      (polynomial source active n d ell' c).trailingCoeff = 0 := by
  obtain ⟨curve, h0, hc, hs⟩ := exists_regular_shifted_root_curve source active n d ell c epsilon a hroot hJac
  let b : RegularChart (source c) ℝ := (projectionForm source c (ell' c) a.2, a.2)
  let gamma : ℝ → RegularChart (source c) ℝ := fun s =>
    (s + projectionForm source c (ell' c) (curve s).2, (curve s).2)
  have hg0 : gamma 0 = b := by simp only [gamma, b, h0, zero_add]
  have hgc : ContinuousAt gamma 0 := by
    unfold gamma projectionForm
    fun_prop
  apply DeformationLowestCoefficient.trailingCoeff_eq_zero_of_tendsto
    (polynomial source active n d ell' c)
    (fun z : RegularChart (source c) ℝ => regularCoefficientMap epsilon z.1)
    (fun p => (regularCoefficientMap_contDiff (source c) epsilon p).continuous)
    (𝓝[≠] (0 : ℝ)) gamma id b
    (hg0 ▸ hgc.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_id.mono_left nhdsWithin_le_nhds) self_mem_nhdsWithin
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds] with s hs
  have hr (i : Fin (TubeParameter.spatialCount (source c))) :
      regularSystem source active n d ell' c epsilon (gamma s) i =
        s * regularChart (source c) (gamma s) i ^ MacaulayBits.Degrees (TubeCleared.layout source) c i := by
    by_cases hi : i.val = 0
    · have he : i = finiteParameterIndex (source c) := Fin.ext hi
      subst i
      rw [regularSystem_head]
      have hx : regularChart (source c) (gamma s) (finiteParameterIndex (source c)) = 1 := rfl
      rw [hx]
      simp only [gamma, add_sub_cancel_right, one_pow, mul_one]
    · rw [← regularSystem_tail_eq source active n d ell ell' c epsilon (curve s) (gamma s) rfl i hi]
      exact hs i
  have hz := polynomial_eval_map_eq_zero_of_common_root source active n d ell' c
    (regularCoefficientMap epsilon (gamma s).1) s (regularChart (source c) (gamma s)) hr
    (regularChart_nonzero (source c) (gamma s))
  rw [Polynomial.eval_map] at hz
  exact hz

end LeanCanny.ETR.TubeCharacteristicQuotient

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeCompiledAffineRoots TubeCharacteristicQuotient
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

/-- Actual compiled roots give roots in the chart used by regular persistence. -/
theorem compiled_regularSystem_root (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z (finiteSystem pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c alpha i) = 0) :
    regularSystem pairFst (fun _ => mask) numerator denominator (fun _ => ell) c alpha
      (projectionValue c z, fun j => z j.succ) = 0 := by
  funext i
  have H := hz i
  rw [eval_finiteSystem] at H
  simp_rw [eval_finiteChartVariables] at H
  exact H

/-- Reprojection preserves annihilation at every simple compiled chart root. -/
theorem annihilatorBivariate_eval_regular_reprojection (c mask : List Bool) (ell ell' : ℕ → ℤ) (alpha : ℝ)
    (a : RegularChart (pairFst c) ℝ)
    (hroot : regularSystem pairFst (fun _ => mask) numerator denominator (fun _ => ell) c alpha a = 0)
    (hJac : (fderiv ℝ (regularSystem pairFst (fun _ => mask) numerator denominator (fun _ => ell) c alpha) a).IsInvertible) :
    (TubeDeformation.projectionPolynomial pairFst (fun _ => mask) numerator denominator
      (fun _ => ell') c alpha).eval (projectionForm pairFst c ell' a.2) = 0 := by
  let φ := TubeDeformation.parameterEvaluation (alpha, projectionForm pairFst c ell' a.2)
  have hq : φ (polynomial pairFst (fun _ => mask) numerator denominator (fun _ => ell') c).trailingCoeff = 0 :=
    trailingCoeff_eq_zero_of_regular_reprojection pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) (fun _ => ell') c alpha a hroot hJac
  have hn : φ (TubeDeformation.characteristicPolynomial pairFst (fun _ => mask)
      numerator denominator (fun _ => ell') c).trailingCoeff = 0 := by
    rw [← (numerator_lowest pairFst (fun _ => mask) numerator denominator (fun _ => ell') c).2,
      polynomial_factorization, Polynomial.trailingCoeff_mul, map_mul, hq, zero_mul]
  rw [TubeDeformation.projectionPolynomial_eval]
  exact (TubeDeformation.characteristicLowest_eval_zero_iff φ pairFst (fun _ => mask)
    numerator denominator (fun _ => ell') c).mp hn

theorem integerAnnihilator_eval_regular_reprojection (c mask : List Bool) (ell ell' : ℕ → ℤ) (a b : ℤ)
    (hb : (b : ℝ) ≠ 0) (z : RegularChart (pairFst c) ℝ)
    (hz : regularSystem pairFst (fun _ => mask) numerator denominator (fun _ => ell) c ((a : ℝ) / b) z = 0)
    (hJac : (fderiv ℝ (regularSystem pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c ((a : ℝ) / b)) z).IsInvertible) :
    (integerAnnihilator c mask ell' a b).eval₂ (Int.castRingHom ℝ) (projectionForm pairFst c ell' z.2) = 0 :=
  TubeCoordinateAnnihilator.specialize_eval_eq_zero _ _ _ _
    (annihilatorBivariate_inner_degree c mask ell') hb _
    (annihilatorBivariate_eval_regular_reprojection c mask ell ell' _ z hz hJac)

/-- Every coordinate of a simple compiled root is covered by the same native
integer originals used by the sampler; global finite fibers are unnecessary. -/
theorem integerCoordinateAnnihilator_eval_compiled_root_of_regular
    (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ) (hb : (b : ℝ) ≠ 0)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z (finiteSystem pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c ((a : ℝ) / b) i) = 0)
    (hJac : (fderiv ℝ (regularSystem pairFst (fun _ => mask) numerator denominator (fun _ => ell) c ((a : ℝ) / b))
      (projectionValue c z, fun j => z j.succ)).IsInvertible)
    (i : Fin (TubeParameter.spatialCount (pairFst c))) :
    (integerCoordinateAnnihilator c mask ell a b i).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  have hr := compiled_regularSystem_root c mask ell ((a : ℝ) / b) z hz
  refine Fin.cases ?_ (fun j => ?_) i
  · have H := integerAnnihilator_eval_regular_reprojection c mask ell ell a b hb _ hr hJac
    have hhead := congrFun hr (finiteParameterIndex (pairFst c))
    rw [regularSystem_head] at hhead
    have he : projectionForm pairFst c ell (fun j => z j.succ) = projectionValue c z :=
      (sub_eq_zero.mp hhead).symm
    rw [he] at H
    exact H
  · have H := integerAnnihilator_eval_regular_reprojection c mask ell (coordinateDirection j.val) a b hb _ hr hJac
    have he : projectionForm pairFst c (coordinateDirection j.val) (fun k => z k.succ) = z j.succ := by
      have H := coordinate_projection (pairFst c) j z
      change (∑ k : Fin (pointCount (TubeIndexed.arity (pairFst c)) + 1),
        (Int.castRingHom ℝ) (coordinateDirection j.val (k.val + 1)) *
          spatialPoint (pairFst c) (decodedPoint (pairFst c) z) k) = z j.succ at H
      rw [spatialPoint_decodedPoint] at H
      exact H
    rw [he] at H
    exact H

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial TubeLevelPacket
open TubeCharacteristicQuotient
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

variable (packet mask read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
variable (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
variable (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)

/-- Native dyadic original polynomials cover every simple compiled root,
without a finite-fiber assumption. -/
theorem dyadicFamily_eval_compiled_root_of_regular (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (pairFst (packet c))) → ℝ)
    (hz : ∀ j, MvPolynomial.eval z (finiteSystem pairFst (fun _ => mask c) numerator denominator
      (fun _ => ell c) (packet c) (dyadicLevel packet mask read ell hp hm hr he c) j) = 0)
    (hJac : (fderiv ℝ (regularSystem pairFst (fun _ => mask c) numerator denominator
      (fun _ => ell c) (packet c) (dyadicLevel packet mask read ell hp hm hr he c))
      (projectionValue (packet c) z, fun j => z j.succ)).IsInvertible)
    (i : Fin (TubeParameter.spatialCount (pairFst (packet c)))) :
    (dyadicFamily packet mask read ell hp hm hr he (pair c (BinaryNatCode.encode i.val))).eval₂
      (Int.castRingHom ℝ) (z i) = 0 := by
  have hα : ((1 : ℤ) : ℝ) / (dyadicDenominator packet mask read ell hp hm hr he c : ℝ) =
      dyadicLevel packet mask read ell hp hm hr he c := by
    simp [dyadicDenominator, dyadicLevel, InfinitesimalSign.dyadic]
  have hb : (dyadicDenominator packet mask read ell hp hm hr he c : ℝ) ≠ 0 := by
    simp only [dyadicDenominator, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hz' := hz
  have hj := hJac
  rw [← hα] at hz' hj
  rw [dyadicFamily, family_coordinate]
  exact integerCoordinateAnnihilator_eval_compiled_root_of_regular (packet c) (mask c) (ell c) 1
    (dyadicDenominator packet mask read ell hp hm hr he c) hb z hz' hj i

end LeanCanny.ETR.TubeCoordinateAnnihilator
