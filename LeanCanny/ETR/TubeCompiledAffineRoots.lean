/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicFinitePersistence
public import LeanCanny.ETR.TubeClearedSystem
public import LeanCanny.ETR.TubeRegularFiber

/-! # Finiteness of the compiled affine tube system

With nonzero substitution denominators, every compiled affine root decodes
to a root of the uncleared spatial equations. The projection row determines
the extra parameter uniquely. Thus finiteness of the geometric spatial
fiber transfers to the compiled system without a Jacobian hypothesis.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCompiledAffineRoots
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
variable {K : Type*} [Field K]

noncomputable def regularRowCode (bits : List Bool) : TubeRegularSource.Index bits → ℕ
  | none => 0
  | some j => TubeProjectionRow.code (TubeIndexed.arity bits) j + 1

theorem regularRowCode_lt (bits : List Bool) (j : TubeRegularSource.Index bits) :
    regularRowCode bits j < pointCount (TubeIndexed.arity bits) + 1 := by
  cases j with
  | none => simp [regularRowCode]
  | some j => exact Nat.add_lt_add_right (TubeProjectionRow.code_lt _ j) 1

noncomputable def regularRowIndex (bits : List Bool) (j : TubeRegularSource.Index bits) : Fin (TubeParameter.spatialCount bits) :=
  ⟨regularRowCode bits j + 1, by have h := regularRowCode_lt bits j; unfold TubeParameter.spatialCount; omega⟩

theorem decoded_regularRowCode (source : List Bool → List Bool) (c : List Bool) (j : TubeRegularSource.Index (source c)) :
    TubeRegularBits.decodedIndex source (fun _ => BinaryNatCode.encode (regularRowCode (source c) j)) c = j := by
  cases j with
  | none =>
    apply TubeRegularBits.decodedIndex_reciprocal
    rfl
  | some j => exact TubeRegularBits.decodedIndex_of_code source _ c j rfl

theorem selected_row (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (j : TubeRegularSource.Index (source c)) :
    TubeBivariate.rows source active n d ell c (regularRowIndex (source c) j) =
      (MvPolynomial.rename (TubeParameter.spatialEquiv (source c))
        (TubeCleared.spatial (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) j (n c) (d c))).map Polynomial.C := by
  have hi : (regularRowIndex (source c) j).val ≠ 0 := Nat.succ_ne_zero _
  rw [TubeBivariate.rows, ite_eq_right hi]
  change (MvPolynomial.rename (TubeParameter.spatialEquiv (source c))
    (TubeCleared.row source active (fun _ => BinaryNatCode.encode (regularRowCode (source c) j + 1 - 1)) n d c)).map Polynomial.C = _
  rw [Nat.add_sub_cancel]
  unfold TubeCleared.row
  rw [decoded_regularRowCode]

theorem scale_ne_zero (bits : List Bool) (d : ℕ → Polynomial ℤ) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount bits → (d i).eval₂ (Int.castRingHom K) epsilon ≠ 0) :
    TubeCleared.scale bits d (Int.castRingHom K) epsilon ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (hd i (Finset.mem_range.mp hi))

theorem eval_selected_row (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon u : K) (y : Fin (pointCount (TubeIndexed.arity (source c)) + 1) → K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (j : TubeRegularSource.Index (source c)) :
    MvPolynomial.eval₂ (TubeCharacteristicQuotient.regularCoefficientMap epsilon u) (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K)
      (TubeBivariate.rows source active n d ell c (regularRowIndex (source c) j)) =
      TubeCleared.scale (source c) (d c) (Int.castRingHom K) epsilon *
        (TubeRegularMacaulay.spatial (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) j).eval₂
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)
          (fun i => (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K) (TubeParameter.spatialEquiv (source c) i)) := by
  have hrow := TubeCleared.row_map_eq source active
    (fun _ => BinaryNatCode.encode (regularRowCode (source c) j)) n d (Int.castRingHom K) epsilon c hd
  unfold TubeCleared.row at hrow
  rw [decoded_regularRowCode] at hrow
  have h := congrArg (MvPolynomial.eval (fun i => (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K) (TubeParameter.spatialEquiv (source c) i))) hrow
  rw [MvPolynomial.eval_map, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_map] at h
  rw [selected_row]
  refine (MvPolynomial.eval₂_map Polynomial.C _ _ _).trans ?_
  have hc : (TubeCharacteristicQuotient.regularCoefficientMap epsilon u).comp Polynomial.C =
      Polynomial.eval₂RingHom (Int.castRingHom K) epsilon := Polynomial.eval₂RingHom_comp_C _ _
  rw [hc]
  refine (MvPolynomial.eval₂_rename _ _ _ _).trans ?_
  unfold TubeParameter.spatialPolynomial at h
  rw [decoded_regularRowCode] at h
  exact h

noncomputable def decodedPoint (bits : List Bool) (z : Fin (TubeParameter.spatialCount bits) → K) :
    Option (TubeSource.Coordinate bits) → K :=
  fun j => z (TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits) j).succ

theorem decoded_chart (bits : List Bool) (z : Fin (TubeParameter.spatialCount bits) → K) :
    (fun i => (Fin.cons (1 : K) (fun j => z j.succ) : Fin (TubeParameter.spatialCount bits) → K)
      (TubeParameter.spatialEquiv bits i)) = (fun i => i.elim 1 (decodedPoint bits z)) := by
  funext i
  cases i <;> rfl

theorem eval_projection_row (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon u : K)
    (y : Fin (pointCount (TubeIndexed.arity (source c)) + 1) → K) :
    MvPolynomial.eval₂ (TubeCharacteristicQuotient.regularCoefficientMap epsilon u)
      (Fin.cons (1 : K) y : Fin (TubeParameter.spatialCount (source c)) → K)
      (TubeBivariate.rows source active n d ell c (TubeCharacteristicQuotient.finiteParameterIndex (source c))) =
      u - ∑ i, (Int.castRingHom K) (ell c (i.val + 1)) * y i := by
  have hr : TubeBivariate.rows source active n d ell c (TubeCharacteristicQuotient.finiteParameterIndex (source c)) =
      (TubeLinear.polynomial source ell c).map (Polynomial.mapRingHom Polynomial.C) := by
    unfold TubeBivariate.rows
    exact ite_eq_left rfl
  rw [hr]
  refine (MvPolynomial.eval₂_map _ _ _ _).trans ?_
  have hc : (TubeCharacteristicQuotient.regularCoefficientMap epsilon u).comp (Polynomial.mapRingHom Polynomial.C) =
      Polynomial.eval₂RingHom (Int.castRingHom K) u := by
    ext <;> simp [TubeCharacteristicQuotient.regularCoefficientMap]
  rw [hc]
  exact TubeLinear.eval_chart source ell c (Int.castRingHom K) u y

theorem spatial_roots_of_compiled (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (z : Fin (TubeParameter.spatialCount (source c)) → K)
    (hz : ∀ i, MvPolynomial.eval z (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0) :
    ∀ j, (TubeRegularMacaulay.spatial (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) j).eval₂
      (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)
      (fun i => i.elim 1 (decodedPoint (source c) z)) = 0 := by
  intro j
  have he := hz (regularRowIndex (source c) j)
  rw [TubeCharacteristicQuotient.eval_finiteSystem] at he
  simp_rw [TubeCharacteristicQuotient.eval_finiteChartVariables] at he
  have hr := eval_selected_row source active n d ell c epsilon
    (z (TubeCharacteristicQuotient.finiteParameterIndex (source c))) (fun j => z j.succ) hd j
  have hv := hr.symm.trans he
  rw [decoded_chart] at hv
  exact (mul_eq_zero.mp hv).resolve_left (scale_ne_zero _ _ _ hd)

theorem finite_fiber_of_finite_spatial_roots (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) → (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (hf : {z : Option (TubeSource.Coordinate (source c)) → K | ∀ j,
      (TubeRegularMacaulay.spatial (source c) (activeSet (TubeIndexed.arity (source c)) (active c)) j).eval₂
        (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon) (fun i => i.elim 1 z) = 0}.Finite) :
    (MvPolynomial.zeroLocus K (ProjectiveNullstellensatz.generated
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon))).Finite := by
  rw [ProjectiveNullstellensatz.zeroLocus_generated]
  apply hf.of_injOn (f := decodedPoint (source c))
  · intro z hz
    exact spatial_roots_of_compiled source active n d ell c epsilon hd z hz
  · intro z hz w hw hzw
    have ht : (fun j : Fin (pointCount (TubeIndexed.arity (source c)) + 1) => z j.succ) = (fun j => w j.succ) := by
      funext j
      obtain ⟨k, rfl⟩ := (TubeMacaulay.coordinateEquiv (TubeIndexed.arity (source c))).surjective j
      exact congrFun hzw k
    have hp (v : Fin (TubeParameter.spatialCount (source c)) → K)
        (hv : ∀ i, MvPolynomial.eval v (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon i) = 0) :
        v (TubeCharacteristicQuotient.finiteParameterIndex (source c)) =
          ∑ i : Fin (pointCount (TubeIndexed.arity (source c)) + 1), (Int.castRingHom K) (ell c (i.val + 1)) * v i.succ := by
      have h := hv (TubeCharacteristicQuotient.finiteParameterIndex (source c))
      rw [TubeCharacteristicQuotient.eval_finiteSystem] at h
      simp_rw [TubeCharacteristicQuotient.eval_finiteChartVariables] at h
      exact sub_eq_zero.mp ((eval_projection_row source active n d ell c epsilon _ _).symm.trans h)
    have h0 := (hp z hz).trans ((congrArg (fun t => ∑ i, (Int.castRingHom K) (ell c (i.val + 1)) * t i) ht).trans (hp w hw).symm)
    funext i
    refine Fin.cases h0 (fun j => congrFun ht j) i

theorem finite_fiber_of_finite_extended_critical (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) →
      (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (hb : TubeRegularFiber.direction (source c)
      (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon) (TubePolynomial.base _) = 1)
    (hf : {z : Option (TubeSource.Coordinate (source c)) → K | ∀ j, MvPolynomial.aeval z
      (GenericProjectionFinite.equation
        (TubeRegularFiber.specializedPolynomial (source c) (activeSet (TubeIndexed.arity (source c)) (active c))
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon))
        (TubePolynomial.base _) (TubeRegularFiber.direction (source c)
          (TubeCleared.parameterMap (source c) (n c) (d c) (Int.castRingHom K) epsilon)) j) = 0}.Finite) :
    (MvPolynomial.zeroLocus K (ProjectiveNullstellensatz.generated
      (TubeCharacteristicQuotient.finiteSystem source active n d ell c epsilon))).Finite := by
  apply finite_fiber_of_finite_spatial_roots source active n d ell c epsilon hd
  exact TubeRegularFiber.finite_spatial_roots_of_finite_extended _ _ _ hb hf
end LeanCanny.ETR.TubeCompiledAffineRoots
