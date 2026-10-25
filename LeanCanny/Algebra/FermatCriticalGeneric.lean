/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCriticalBadSystem
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Generic root-freeness of the homogeneous singular-critical system

Generic directions give nonsingular affine critical roots on a regular
hypersurface. The pure-power leading equations exclude every root at infinity.
Together these prove root-freeness of the actual homogenized Jacobian system.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatCriticalGeneric
open MvPolynomial FermatCriticalHomogenization FermatCriticalBadSystem
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

noncomputable def direction (ψ : MvPolynomial (Fin n) K →+* L) : Fin (n + 1) → L :=
  fun i => ψ ((Fin.cons (1 : MvPolynomial (Fin n) K) (fun j => X j) :
    Fin (n + 1) → MvPolynomial (Fin n) K) i)

omit [CharZero K] in
theorem independent_direction (ψ : MvPolynomial (Fin n) K →+* L) (hψ : Function.Injective ψ)
    (hψC : ψ.comp C = algebraMap K L) :
    AlgebraicIndependent K (fun i : {j : Fin (n + 1) // j ≠ 0} => direction ψ i.val) := by
  have hcomm (k : K) : ψ (algebraMap K (MvPolynomial (Fin n) K) k) = algebraMap K L k := by
    change ψ (C k) = algebraMap K L k
    exact congrArg (fun g : K →+* L => g k) hψC
  let f : MvPolynomial (Fin n) K →ₐ[K] L := { toRingHom := ψ, commutes' := hcomm }
  have hf : Function.Injective f := hψ
  have hX : AlgebraicIndependent K (f ∘ fun i : Fin n => X i) :=
    (MvPolynomial.algebraicIndependent_X (Fin n) K).map hf.injOn
  let e := finSuccAboveEquiv (0 : Fin (n + 1))
  have hfn : (fun i : {j : Fin (n + 1) // j ≠ 0} => direction ψ i.val) =
      (f ∘ fun i : Fin n => X i) ∘ e.symm := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    change ψ ((Fin.cons (1 : MvPolynomial (Fin n) K) (fun k => X k) :
      Fin (n + 1) → MvPolynomial (Fin n) K) (e j).val) = ψ (X (e.symm (e j)))
    rw [Equiv.symm_apply_apply]
    simp only [e, finSuccAboveEquiv_apply, Fin.zero_succAbove, Fin.cons_succ]
  rw [hfn]
  exact hX.comp e.symm e.symm.injective

omit [CharZero K] in
theorem eval_parameter_polynomial (ψ : MvPolynomial (Fin n) K →+* L)
    (hψC : ψ.comp C = algebraMap K L) (p : MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → L) :
    (p.map C).eval₂ ψ x = aeval x p := by
  rw [eval₂_map, hψC]
  rfl

omit [CharZero K] in
theorem eval_jacobian (ψ : MvPolynomial (Fin n) K →+* L) (hψC : ψ.comp C = algebraMap K L)
    (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ) (x : Fin (n + 1) → L) :
    (jacobian low a N).eval₂ ψ x =
      (GenericProjectionJacobian.spatial (polynomial low a N) 0 (direction ψ) x).det := by
  change (eval₂Hom ψ x) (Matrix.det (fun i j => pderiv j (equations low a N i))) = _
  rw [(eval₂Hom ψ x).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (pderiv j (equations low a N i)).eval₂ ψ x = _
  rw [equations_eq]
  by_cases hi : i = 0
  · simp only [ProjectionCriticalFamily.spatialEquation, ite_eq_left hi, pderiv_map,
      GenericProjectionJacobian.spatial]
    exact eval_parameter_polynomial ψ hψC _ x
  · simp only [ProjectionCriticalFamily.spatialEquation, ite_eq_right hi, map_sub, pderiv_C_mul,
      pderiv_map, eval₂_sub, eval₂_mul, eval₂_C, GenericProjectionJacobian.spatial,
      eval_parameter_polynomial ψ hψC, direction]

theorem affine_regular (ψ : MvPolynomial (Fin n) K →+* L) (hψC : ψ.comp C = algebraMap K L)
    (low : MvPolynomial (Fin (n + 1)) K) (a : K) (N : ℕ)
    (hind : AlgebraicIndependent K (fun i : {j : Fin (n + 1) // j ≠ 0} => direction ψ i.val))
    (hregular : ∀ x : Fin (n + 1) → L, aeval x (polynomial low a N) = 0 →
      ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0)
    (x : Fin (n + 1) → L) (hx : ∀ j, (equations low a N j).eval₂ ψ x = 0) :
    (jacobian low a N).eval₂ ψ x ≠ 0 := by
  have hrows := hx
  rw [equations_eq] at hrows
  obtain ⟨hq, hpartial⟩ := (ProjectionCriticalFamily.spatial_zero_iff ψ
    ((polynomial low a N).map C) 0 (Fin.cons 1 (fun j => X j)) (by simp) x).mp hrows
  have hq' : aeval x (polynomial low a N) = 0 := by
    simpa only [eval_parameter_polynomial ψ hψC] using hq
  have hc (j : Fin (n + 1)) : aeval x (pderiv j (polynomial low a N)) =
      direction ψ j * aeval x (pderiv 0 (polynomial low a N)) := by
    simpa only [pderiv_map, eval_parameter_polynomial ψ hψC, direction] using hpartial j
  have hb : aeval x (pderiv 0 (polynomial low a N)) ≠ 0 := by
    intro hb
    obtain ⟨j, hj⟩ := hregular x hq'
    rw [hc j, hb, mul_zero] at hj
    exact hj rfl
  rw [eval_jacobian ψ hψC]
  exact FixedLevelProjectionJacobian.spatial_det_ne_zero _ 0 _ x hind hq' hc hb

omit [Algebra K L] in
theorem no_root_at_infinity (ψ : MvPolynomial (Fin n) K →+* L) (hψ : Function.Injective ψ)
    (low : MvPolynomial (Fin (n + 1)) K) (a : K) (ha : a ≠ 0) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N)
    (y : Option (Fin (n + 1)) → L) (hy0 : y none = 0)
    (hy : ∀ j, (FermatCriticalBadSystem.rows low a N (some j)).eval₂ ψ y = 0) : y = 0 := by
  let x : Fin (n + 1) → L := fun j => y (some j)
  have hyr : y = fun j => j.elim 0 x := by
    funext j
    cases j with
    | none => exact hy0
    | some j => rfl
  have hlowL : ((low.map C).map ψ).totalDegree < N :=
    (PolynomialMapDegree.degree_le ψ _).trans_lt ((PolynomialMapDegree.degree_le C low).trans_lt hlow)
  have hx (j : Fin (n + 1)) : (FermatCriticalInfinity.system a N j).eval₂ ψ x = 0 := by
    have he : (FermatCriticalBadSystem.rows low a N (some j)).eval₂ ψ y = (FermatCriticalInfinity.system a N j).eval₂ ψ x := by
      change (FermatCriticalHomogenization.rows (low.map C) (C a) N (fun i => X i) j).eval₂ ψ y = _
      calc
        _ = eval y (FermatCriticalHomogenization.rows ((low.map C).map ψ) (ψ (C a)) N (fun i => ψ (X i)) j) := by
          rw [← eval_map, map_rows]
        _ = eval x (FermatCriticalInfinity.native (ψ (C a)) N (fun i => ψ (X i)) j) := by
          rw [hyr]
          exact eval_infinity _ _ N hlowL hN _ x j
        _ = (FermatCriticalInfinity.system a N j).eval₂ ψ x := by
          rw [← eval_map, FermatCriticalInfinity.system, FermatCriticalInfinity.map_native]
    exact he.symm.trans (hy j)
  have hx0 := FermatCriticalInfinity.no_root_injective a ha N hN (AlgebraicClosure K) ψ hψ x hx
  funext j
  cases j with
  | none => exact hy0
  | some j => exact congrFun hx0 j

theorem no_root (ψ : MvPolynomial (Fin n) K →+* L) (hψ : Function.Injective ψ)
    (hψC : ψ.comp C = algebraMap K L)
    (low : MvPolynomial (Fin (n + 1)) K) (a : K) (ha : a ≠ 0) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N)
    (hind : AlgebraicIndependent K (fun i : {j : Fin (n + 1) // j ≠ 0} => direction ψ i.val))
    (hregular : ∀ x : Fin (n + 1) → L, aeval x (polynomial low a N) = 0 →
      ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0)
    (y : Option (Fin (n + 1)) → L) (hy : ∀ j, (FermatCriticalBadSystem.rows low a N j).eval₂ ψ y = 0) : y = 0 := by
  exact HomogeneousBadSystem.no_nonzero_root ψ (equations low a N) (FermatCriticalInfinity.degrees n N)
    (jacobian low a N) (jacobianDegree n N) (equations_degree low a N hlow) (jacobian_degree low a N hlow)
    (affine_regular ψ hψC low a N hind hregular) (no_root_at_infinity ψ hψ low a ha N hlow hN) y hy

theorem native_no_root (ψ : MvPolynomial (Fin n) K →+* L) (hψ : Function.Injective ψ)
    (hψC : ψ.comp C = algebraMap K L)
    (low : MvPolynomial (Fin (n + 1)) K) (a : K) (ha : a ≠ 0) (N : ℕ)
    (hlow : low.totalDegree < N) (hN : 1 < N)
    (hind : AlgebraicIndependent K (fun i : {j : Fin (n + 1) // j ≠ 0} => direction ψ i.val))
    (hregular : ∀ x : Fin (n + 1) → L, aeval x (polynomial low a N) = 0 →
      ∃ j, aeval x (pderiv j (polynomial low a N)) ≠ 0)
    (x : Fin (n + 2) → L) (hx : ∀ j, (nativeRows low a N j).eval₂ ψ x = 0) : x = 0 := by
  let y : Option (Fin (n + 1)) → L := fun j => x (layout j)
  have hy (j : Option (Fin (n + 1))) : (FermatCriticalBadSystem.rows low a N j).eval₂ ψ y = 0 := by
    simpa only [nativeRows, eval₂_rename, Function.comp_def, Equiv.symm_apply_apply, y] using hx (layout j)
  have hy0 := no_root ψ hψ hψC low a ha N hlow hN hind hregular y hy
  funext j
  have h := congrFun hy0 (layout.symm j)
  simpa only [y, Equiv.apply_symm_apply, Pi.zero_apply] using h

end LeanCanny.Algebra.FermatCriticalGeneric
