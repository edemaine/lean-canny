/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ProjectionCoordinateAlgebraic
public import LeanCanny.Algebra.FiniteAlgebraicZeros
import Mathlib.Tactic.Ring

/-! # Finite regular projection fibers in algebraically independent directions

Adjoin the reciprocal of the base partial derivative to the normalized
projection equations. Generic-coordinate algebraicity applies in every
minimal-prime quotient field, so the extended solution set is finite.
Projecting away the reciprocal gives finiteness of the regular critical roots.
The result is qualitative and gives no effective exceptional-direction bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.GenericProjectionFinite
open MvPolynomial
open scoped BigOperators

variable {K B ι : Type*} [Field K] [Field B] [Algebra K B] [Fintype ι]

noncomputable def liftPolynomial (p : MvPolynomial ι K) : MvPolynomial (Option ι) B :=
  rename some (p.map (algebraMap K B))

noncomputable def equation (p : MvPolynomial ι K) (base : ι) (v : ι → B) :
    Sum Bool ι → MvPolynomial (Option ι) B
  | .inl false => liftPolynomial p
  | .inl true => X none * liftPolynomial (pderiv base p) - 1
  | .inr i => liftPolynomial (pderiv i p) - C (v i) * liftPolynomial (pderiv base p)

noncomputable def ideal (p : MvPolynomial ι K) (base : ι) (v : ι → B) : Ideal (MvPolynomial (Option ι) B) :=
  Ideal.span (Set.range (equation p base v))

omit [Fintype ι] in
theorem zeroSet_iff (p : MvPolynomial ι K) (base : ι) (v : ι → B) (z : Option ι → B) :
    z ∈ FiniteAlgebraicZeros.zeroSet (ideal p base v) ↔ ∀ j, aeval z (equation p base v j) = 0 := by
  constructor
  · intro h j
    exact h _ (Ideal.subset_span (Set.mem_range_self j))
  · intro h
    have hI : ideal p base v ≤ RingHom.ker (aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact h j
    exact fun q hq => hI hq

section Extension
variable {L : Type*} [Field L] [Algebra K L] [Algebra B L] [IsScalarTower K B L]

omit [Fintype ι] in
theorem eval_liftPolynomial (p : MvPolynomial ι K) (z : Option ι → L) :
    aeval z (liftPolynomial (B := B) p) = aeval (fun i => z (some i)) p := by
  change (rename some (p.map (algebraMap K B))).eval₂ (algebraMap B L) z = _
  rw [eval₂_rename, eval₂_map, ← IsScalarTower.algebraMap_eq K B L]
  rfl

omit [Fintype ι] in
theorem algebraic_polynomial_value (p : MvPolynomial ι K) (x : ι → L)
    (hx : ∀ i, IsAlgebraic B (x i)) : IsAlgebraic B (aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [aeval_C, IsScalarTower.algebraMap_apply K B L]
    exact isAlgebraic_algebraMap _
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, aeval_X] using hp.mul (hx i)

theorem algebraic_extended_coordinates [CharZero K] (p : MvPolynomial ι K) (base : ι) (v : ι → B)
    (z : Option ι → L) (hbase : v base = 1)
    (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i))
    (hz : ∀ j, aeval z (equation p base v j) = 0) : ∀ j, IsAlgebraic B (z j) := by
  let x : ι → L := fun i => z (some i)
  have hp : aeval x p = 0 := by
    simpa only [equation, eval_liftPolynomial] using hz (.inl false)
  have hinv : z none * aeval x (pderiv base p) = 1 := by
    have h := hz (.inl true)
    rw [equation, map_sub, map_mul, aeval_X, eval_liftPolynomial, map_one] at h
    exact sub_eq_zero.mp h
  have hpartial (i : ι) : aeval x (pderiv i p) = algebraMap B L (v i) * aeval x (pderiv base p) := by
    have h := hz (.inr i)
    rw [equation, map_sub, map_mul, aeval_C, eval_liftPolynomial, eval_liftPolynomial] at h
    exact sub_eq_zero.mp h
  have hw (i : ι) : algebraMap B L (v i) = z none * aeval x (pderiv i p) := by
    calc
      _ = algebraMap B L (v i) * (z none * aeval x (pderiv base p)) := by rw [hinv, mul_one]
      _ = z none * aeval x (pderiv i p) := by rw [hpartial i]; ring
  have hc := ProjectionCoordinateAlgebraic.algebraic_normalized_coordinates (fun _ : Unit => p) x v
    (fun _ => z none) (fun _ => hp) (fun i => by simpa using hw i) base hbase hind
  intro j
  cases j with
  | some i => exact hc i
  | none =>
    rw [eq_inv_of_mul_eq_one_left hinv]
    exact (algebraic_polynomial_value (pderiv base p) x hc).inv

end Extension

theorem finite_extended_solutions [CharZero K] (p : MvPolynomial ι K) (base : ι) (v : ι → B)
    (hbase : v base = 1) (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i)) :
    {z : Option ι → B | ∀ j, aeval z (equation p base v j) = 0}.Finite := by
  have hfin : (FiniteAlgebraicZeros.zeroSet (ideal p base v)).Finite := by
    apply FiniteAlgebraicZeros.finite_zeroSet
    intro P hP
    let : P.IsPrime := hP.isPrime
    let z := FiniteAlgebraicZeros.quotientPoint P
    have hz : ∀ j, aeval z (equation p base v j) = 0 := by
      intro j
      rw [FiniteAlgebraicZeros.eval_quotientPoint]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hP.le (Ideal.subset_span (Set.mem_range_self j))), map_zero]
    exact algebraic_extended_coordinates p base v z hbase hind hz
  exact hfin.subset (fun z hz => (zeroSet_iff p base v z).mpr hz)

theorem finite_regular_projection_roots [CharZero K] (p : MvPolynomial ι K) (base : ι) (v : ι → B)
    (hbase : v base = 1) (hind : AlgebraicIndependent K (fun i : {i : ι // i ≠ base} => v i)) :
    {x : ι → B | aeval x p = 0 ∧
      (∀ i, aeval x (pderiv i p) = v i * aeval x (pderiv base p)) ∧ aeval x (pderiv base p) ≠ 0}.Finite := by
  apply ((finite_extended_solutions p base v hbase hind).image (fun z i => z (some i))).subset
  rintro x ⟨hp, hpartial, hne⟩
  let z : Option ι → B := fun j => j.elim ((aeval x (pderiv base p))⁻¹) x
  have hzx : (fun i => z (some i)) = x := rfl
  refine ⟨z, ?_, rfl⟩
  intro j
  rcases j with b | i
  · cases b
    · rw [equation, eval_liftPolynomial, hzx]
      exact hp
    · rw [equation, map_sub, map_mul, aeval_X, eval_liftPolynomial, hzx, map_one]
      exact sub_eq_zero.mpr (inv_mul_cancel₀ hne)
  · rw [equation, map_sub, map_mul, aeval_C, eval_liftPolynomial, eval_liftPolynomial, hzx]
    exact sub_eq_zero.mpr (hpartial i)

end LeanCanny.Algebra.GenericProjectionFinite
