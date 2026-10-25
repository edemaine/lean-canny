/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.GenericProjectionJacobian

/-! # Generic critical projections on a fixed polynomial level

Only the non-base direction coordinates are algebraically independent.
Their derivations provide the tangent columns of the critical Jacobian;
the nonzero base partial supplies the remaining normal direction. Thus the
Jacobian is invertible without varying the hypersurface level. This permits
the coefficient field to contain a separate sweep parameter.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedLevelProjectionJacobian
open MvPolynomial Matrix
open scoped BigOperators Classical

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [CharZero K]
  [Fintype ι] [DecidableEq ι]

theorem spatial_det_ne_zero (q : MvPolynomial ι K) (base : ι) (v x : ι → L)
    (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i))
    (hq : aeval x q = 0)
    (hcritical : ∀ i, aeval x (pderiv i q) = v i * aeval x (pderiv base q))
    (hb : aeval x (pderiv base q) ≠ 0) :
    (GenericProjectionJacobian.spatial q base v x).det ≠ 0 := by
  choose δ hδ using fun j => CoordinateDerivation.exists_of_independent hind j
  let A := GenericProjectionJacobian.spatial q base v x
  let b := aeval x (pderiv base q)
  have hv (j : {i : ι // i ≠ base}) (i : ι) (hi : i ≠ base) :
      δ j (v i) = if i = j.val then 1 else 0 := by
    simpa only [Subtype.ext_iff] using hδ j ⟨i, hi⟩
  have htangent (j : {i : ι // i ≠ base}) :
      A *ᵥ (fun k => δ j (x k)) = Pi.single j.val b := by
    funext i
    change (∑ k, A i k * δ j (x k)) = (Pi.single j.val b : ι → L) i
    by_cases hi : i = base
    · subst i
      simp only [A, GenericProjectionJacobian.spatial, ite_true]
      rw [← CriticalValueAlgebraic.chain_rule, hq, map_zero]
      simp [Ne.symm j.property]
    · have hdcrit := congrArg (δ j) (hcritical i)
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hv j i hi,
        CriticalValueAlgebraic.chain_rule, CriticalValueAlgebraic.chain_rule] at hdcrit
      simp only [A, GenericProjectionJacobian.spatial, ite_eq_right hi]
      rw [show (∑ k, (aeval x (pderiv k (pderiv i q)) -
          v i * aeval x (pderiv k (pderiv base q))) * δ j (x k)) =
        (∑ k, aeval x (pderiv k (pderiv i q)) * δ j (x k)) -
          v i * ∑ k, aeval x (pderiv k (pderiv base q)) * δ j (x k) by
            simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]]
      have he : (∑ k, aeval x (pderiv k (pderiv i q)) * δ j (x k)) -
          v i * ∑ k, aeval x (pderiv k (pderiv base q)) * δ j (x k) =
          (if i = j.val then 1 else 0) * b := by
        dsimp only [b]
        linear_combination hdcrit
      rw [he]
      by_cases hij : i = j.val
      · simp [hij]
      · simp [hij]
  have hkernel (w : ι → L) (hw : w ᵥ* A = 0) : w = 0 := by
    have hother (i : ι) (hi : i ≠ base) : w i = 0 := by
      have he : w ⬝ᵥ (A *ᵥ (fun k => δ ⟨i, hi⟩ (x k))) = 0 := by
        rw [Matrix.dotProduct_mulVec, hw]
        simp
      rw [htangent, dotProduct_single] at he
      exact (mul_eq_zero.mp he).resolve_right hb
    have he := congrFun hw base
    change (∑ i, w i * A i base) = 0 at he
    have hsum : ∑ i, w i * A i base = w base * b := by
      rw [Finset.sum_eq_single base]
      · simp only [A, GenericProjectionJacobian.spatial, ite_true, b]
      · intro i _ hi
        rw [hother i hi, zero_mul]
      · simp
    rw [hsum] at he
    have hbase := (mul_eq_zero.mp he).resolve_right hb
    funext i
    change w i = 0
    by_cases hi : i = base
    · simpa only [hi] using hbase
    · exact hother i hi
  have hinj : Function.Injective A.vecMul := by
    intro w z he
    change w ᵥ* A = z ᵥ* A at he
    apply sub_eq_zero.mp
    apply hkernel
    rw [Matrix.sub_vecMul, he, sub_self]
  exact ((A.isUnit_iff_isUnit_det).mp (Matrix.vecMul_injective_iff_isUnit.mp hinj)).ne_zero

theorem extended_det_ne_zero (q : MvPolynomial ι K) (base : ι) (v x : ι → L) (u : L)
    (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i))
    (hq : aeval x q = 0)
    (hcritical : ∀ i, aeval x (pderiv i q) = v i * aeval x (pderiv base q))
    (hreciprocal : u * aeval x (pderiv base q) = 1) :
    (GenericProjectionJacobian.extended q base v x u).det ≠ 0 := by
  have hb : aeval x (pderiv base q) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hreciprocal
    exact zero_ne_one hreciprocal
  rw [GenericProjectionJacobian.extended_det]
  exact mul_ne_zero (spatial_det_ne_zero q base v x hind hq hcritical hb) hb

theorem formalJacobian_det_ne_zero (q : MvPolynomial ι K) (base : ι) (v x : ι → L) (u : L)
    (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i))
    (hq : aeval x q = 0)
    (hcritical : ∀ i, aeval x (pderiv i q) = v i * aeval x (pderiv base q))
    (hreciprocal : u * aeval x (pderiv base q) = 1) :
    (Matrix.of fun i j => aeval (fun k : Option ι => k.elim u x)
      (pderiv j (GenericProjectionJacobian.equation q base 0 v i))).det ≠ 0 := by
  change Matrix.det (fun i j => aeval (fun k : Option ι => k.elim u x)
    (pderiv j (GenericProjectionJacobian.equation q base 0 v i))) ≠ 0
  rw [GenericProjectionJacobian.formalJacobian_eq]
  exact extended_det_ne_zero q base v x u hind hq hcritical hreciprocal

end LeanCanny.Algebra.FixedLevelProjectionJacobian
