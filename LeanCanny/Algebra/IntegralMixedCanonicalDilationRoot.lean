/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalDilation

/-! # Exact coordinate and critical-row transport for one fixed dilation frame

The frozen count, spatial source and interpreting parent hom stay fixed. This
bridge does not assert that later original coordinates can be frozen by constant
Y heights; those would require retained-valued eta slopes or an explicitly
correlated new source recipe.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalDilation
open IntegralMixedHistory IntegralMixedCriticalSweep Filter
open scoped Topology
variable {n k m S B : ℕ} {P : SpatialSource (n+1)} {ι : Type}

def coordinateIndex (hkn : k ≤ n) (select : Fin k → Fin m) (j : Fin n) (hj : k ≤ j.val) :
    Fin ((n+1)-(rule hkn select).critical.offset.val+1) := ⟨j.val-k,by
  simp only [rule]
  have H:=j.isLt
  omega⟩

theorem free_index (hkn : k ≤ n) (select : Fin k → Fin m) (j : Fin n) (hj : k ≤ j.val) :
    ClearedCoordinateCritical.freeIndex (rule hkn select).critical.offset.val (fit (rule hkn select)).le
      (coordinateIndex hkn select j hj)=j.succ.castSucc := by
  apply Fin.ext
  simp only [ClearedCoordinateCritical.freeIndex,coordinateIndex,rule,Fin.val_succ,Fin.val_castSucc]
  omega

theorem free_objective (hkn : k ≤ n) (select : Fin k → Fin m) :
    ClearedCoordinateCritical.freeIndex (rule hkn select).critical.offset.val (fit (rule hkn select)).le
      (objective (rule hkn select))=Fin.last (n+1) := by
  apply Fin.ext
  change (rule hkn select).critical.offset.val+(objective (rule hkn select)).val=n+1
  rw [objective_last]
  change k+1+(n-k)=n+1
  omega

theorem coordinate_scaling (x : State P S B m ι) (hkn : k ≤ n) (select : Fin k → Fin m)
    (j : Fin n) (hj : k ≤ j.val) (eta : ℝ) (old : Fin n → ℝ) (v : ℝ) :
    (commonDenominator x:ℝ)*point (k:=k) x eta old v
      (ClearedCoordinateCritical.freeIndex (rule hkn select).critical.offset.val (fit (rule hkn select)).le
        (coordinateIndex hkn select j hj))=eta*old j := by
  rw [free_index,point,Fin.snoc_castSucc]
  simp only [FixedLeadingTiltedGradient.point,Fin.cases_succ,ite_eq_right (by omega : ¬j.val<k)]
  have HQ : (commonDenominator x:ℝ)≠0 := Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  rw [← mul_assoc,← mul_div_assoc,mul_div_cancel_left₀ _ HQ]

theorem gradient (hkn : k ≤ n) (select : Fin k → Fin m) (z : Fin (n+2) → ℝ)
    (hg : ∀ j : Fin (n+1), k+1 ≤ j.val →
      (MvPolynomial.pderiv j.castSucc (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) z=0) :
    ∀ i : Fin ((n+1)-(rule hkn select).critical.offset.val+1), i≠objective (rule hkn select) →
      (MvPolynomial.pderiv (ClearedCoordinateCritical.freeIndex (rule hkn select).critical.offset.val
        (fit (rule hkn select)).le i) (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) z=0 := by
  intro i hi
  have HB : i.val<n-k+1 := by simpa only [rule,Nat.add_sub_add_right] using i.isLt
  have HN : i.val≠n-k := fun h => hi (Fin.ext (h.trans (objective_last hkn select).symm))
  let j : Fin (n+1) := ⟨k+1+i.val,by omega⟩
  have HE : ClearedCoordinateCritical.freeIndex (rule hkn select).critical.offset.val
      (fit (rule hkn select)).le i=j.castSucc := Fin.ext rfl
  rw [HE]
  exact hg j (by change k+1 ≤ k+1+i.val; omega)

theorem critical_root (x : State P S B m ι) (hm : m ≤ S) (hkn : k ≤ n) (select : Fin k → Fin m)
    (j : Fin n) (hj : k ≤ j.val) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (values : Fin m → ℝ)
    (H : ∀ i, φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (eta : ℝ) (old : Fin n → ℝ) (v : ℝ)
    (Hparam : ∀ i : Fin n, ∀ hi : i.val<k, old i=values (select ⟨i.val,hi⟩))
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ)
      (point (k:=k) x eta old v)=0)
    (hg : ∀ i : Fin (n+1), k+1 ≤ i.val →
      (MvPolynomial.pderiv i.castSucc (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) (point (k:=k) x eta old v)=0) :
    (IntegralMixedLimitCoordinate.selectedSeries x hm (rule hkn select) (coordinateIndex hkn select j hj) φ).eval₂
      (Polynomial.evalRingHom (old j)) eta=0 :=
  IntegralMixedLimitCoordinate.critical_root x hm (rule hkn select) (coordinateIndex hkn select j hj) φ eta (old j)
    (point (k:=k) x eta old v) (coordinate_scaling x hkn select j hj eta old v)
    (frozen x hm hkn select φ values H eta old v Hparam) hp (gradient hkn select _ hg)

end LeanCanny.Algebra.IntegralMixedCanonicalDilation
