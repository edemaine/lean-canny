/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrices
public import LeanCanny.Geometry.BoundedMarkedLiftCoordinates

/-! # The old slack matrices encode the prescribed real slack values

One old-algebra interpretation is used for every original coordinate and
both slack elements. These are identities of that interpretation, before
any new scalar roots are adjoined.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedSlackInterpretation
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBits
open IntegralMixedFramedClearedMatrixBits (family)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (N R : List Bool→ℕ) (key : List Bool)
  (φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (x : Fin (N key)→ℝ)
  (hx : ∀ i : Fin (N key),φ (elementAt P D H key (N key-i.val))=(commonAt P D H key : ℝ)*x i)

include hx

theorem sum_value (e : ℕ) :
    φ (∑ i ∈ Finset.range (N key),elementAt P D H key (N key-i)^e)=
      (commonAt P D H key : ℝ)^e*∑ i : Fin (N key),x i^e := by
  rw [map_sum,←Fin.sum_univ_eq_sum_range]
  simp_rw [map_pow,hx,mul_pow]
  rw [Finset.mul_sum]

theorem sphere_value : φ (sphereElement P D H N R key)=
    (commonAt P D H key : ℝ)^2*(((2 : ℝ)^R key)^2-∑ i : Fin (N key),x i^2) := by
  rw [sphereElement,map_sub,map_intCast,sum_value P D H N key φ x hx 2]
  simp only [sphereCoefficient,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  ring

theorem regular_value (d L K : List Bool→ℕ) (hd : 2*(d key/2)=d key) (u : ℝ)
    (hu : φ (sphereElement P D H N R key)=(commonAt P D H key : ℝ)^2*u^2) :
    φ (regularElement P D H N d R L K key)=
      (commonAt P D H key : ℝ)^d key*((2 : ℝ)^L key*(2 : ℝ)^K key+1-
        (2 : ℝ)^L key*(∑ i : Fin (N key),x i^d key)-(2 : ℝ)^L key*u^d key) := by
  rw [regularElement,map_sub,map_sub,map_intCast,map_zsmul,map_zsmul,map_pow,hu,
    sum_value P D H N key φ x hx]
  simp only [regularCoefficient,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,zsmul_eq_mul]
  rw [mul_pow,←pow_mul,←pow_mul,hd]
  ring

omit hx

theorem sphere_marked (q : MvPolynomial (Fin (N key)) ℤ) (a : BoundedZeroSource.Bounded q (R key))
    (ha : ∀ i : Fin (N key),φ (elementAt P D H key (N key-i.val))=(commonAt P D H key : ℝ)*a.val i) :
    φ (sphereElement P D H N R key)=
      (commonAt P D H key : ℝ)^2*(BoundedRegularSource.sphereSlack q (R key) a)^2 := by
  rw [sphere_value P D H N R key φ a.val ha,BoundedRegularSource.sphereSlack_sq]
  simp only [BoundedZeroSource.radiusSquared,BoundedZeroSource.radial,Int.cast_pow,Int.cast_ofNat,
    ←pow_mul,Nat.mul_comm 2 (R key)]

theorem regular_marked (q : MvPolynomial (Fin (N key)) ℤ) (E b : ℕ) (a : BoundedZeroSource.Bounded q (R key))
    (ha : ∀ i : Fin (N key),φ (elementAt P D H key (N key-i.val))=(commonAt P D H key : ℝ)*a.val i)
    (d L K : List Bool→ℕ) (hd : d key=BoundedZeroSource.powerDegree E)
    (hL : L key=BoundedRegularSource.regularizationExponent (N key) E b (R key))
    (hK : K key=BoundedZeroSource.penaltyExponent (N key) E (R key)) :
    φ (regularElement P D H N d R L K key)=
      (2 : ℝ)^L key*(commonAt P D H key : ℝ)^d key*(BoundedRegularSource.regularSlack q E b (R key) a).re^d key := by
  have HE:=regular_value P D H N R key φ a.val ha d L K
    (by rw [hd]; unfold BoundedZeroSource.powerDegree; omega)
    (BoundedRegularSource.sphereSlack q (R key) a) (sphere_marked P D H N R key φ q a ha)
  rw [HE,hd,hL,hK]
  rw [←BoundedRegularSource.regularSlack_scaled q E b (R key) a]
  ring

end LeanCanny.Geometry.IntegralMixedFramedSlackInterpretation
