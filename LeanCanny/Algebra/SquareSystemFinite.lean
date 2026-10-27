/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAlgebraicZeros
public import LeanCanny.Algebra.CriticalValueAlgebraic
public import LeanCanny.Algebra.JacobianKernelCharts

/-! # Finiteness of the regular roots of a square polynomial system

Adjoining the inverse Jacobian determinant removes every singular component.
In each minimal-prime quotient field, the chain rule and invertible Jacobian
force all coordinate derivations to vanish. Characteristic zero then makes
every coordinate algebraic, so the extended zero set and its projection are
finite. Singular roots elsewhere in the original zero set are allowed.
-/

@[expose] public section
namespace LeanCanny.Algebra.SquareSystemFinite
open MvPolynomial
open scoped Classical BigOperators Matrix

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

theorem algebraic_eval (p : MvPolynomial (Fin n) K) (x : Fin n → L)
    (hx : ∀ i, IsAlgebraic K (x i)) : IsAlgebraic K (aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [aeval_C]; exact isAlgebraic_algebraMap a
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul, aeval_X] using hp.mul (hx i)

theorem algebraic_of_regular [CharZero K] (q : Fin n → MvPolynomial (Fin n) K) (x : Fin n → L)
    (hx : ∀ j, aeval x (q j) = 0) (hdet : aeval x (JacobianKernelCharts.jacobian q) ≠ 0) :
    ∀ i, IsAlgebraic K (x i) := by
  have hM : (JacobianKernelCharts.matrix (algebraMap K L) q x).det ≠ 0 := by
    simpa only [MvPolynomial.aeval_def, JacobianKernelCharts.eval_jacobian] using hdet
  intro i
  apply TranscendentalDerivation.algebraic_of_all_derivations_vanish
  intro δ
  have hv : JacobianKernelCharts.matrix (algebraMap K L) q x *ᵥ (fun j => δ (x j)) = 0 := by
    funext j
    change (∑ k, aeval x (pderiv k (q j)) * δ (x k)) = 0
    rw [← CriticalValueAlgebraic.chain_rule, hx j, map_zero]
  have he : (fun j => δ (x j)) = 0 :=
    Matrix.mulVec_injective_of_det_ne_zero hM (hv.trans (Matrix.mulVec_zero _).symm)
  exact congrFun he i

noncomputable def system (q : Fin n → MvPolynomial (Fin n) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  Fin.cons (X 0 * rename Fin.succ (JacobianKernelCharts.jacobian q) - 1)
    (fun j => rename Fin.succ (q j))

theorem system_iff (q : Fin n → MvPolynomial (Fin n) K) (z : Fin (n + 1) → L) :
    (∀ j, aeval z (system q j) = 0) ↔
      z 0 * aeval (fun i => z i.succ) (JacobianKernelCharts.jacobian q) = 1 ∧
        ∀ j, aeval (fun i => z i.succ) (q j) = 0 := by
  simp only [system, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, map_sub, map_mul,
    aeval_X, map_one, aeval_rename, sub_eq_zero, Function.comp_def]

noncomputable def ideal (q : Fin n → MvPolynomial (Fin n) K) : Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span (Set.range (system q))

theorem quotient_algebraic [CharZero K] (q : Fin n → MvPolynomial (Fin n) K)
    (P : Ideal (MvPolynomial (Fin (n + 1)) K)) (hP : P ∈ (ideal q).minimalPrimes) :
    ∀ i, IsAlgebraic K (FiniteAlgebraicZeros.quotientPoint P i) := by
  let : P.IsPrime := hP.isPrime
  let z := FiniteAlgebraicZeros.quotientPoint P
  have hz : ∀ j, aeval z (system q j) = 0 := by
    intro j
    rw [FiniteAlgebraicZeros.eval_quotientPoint]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hP.le (Ideal.subset_span (Set.mem_range_self j))), map_zero]
  obtain ⟨hinv, hroot⟩ := (system_iff q z).mp hz
  have hdet : aeval (fun i => z i.succ) (JacobianKernelCharts.jacobian q) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hinv
    exact zero_ne_one hinv
  have ha := algebraic_of_regular q (fun i => z i.succ) hroot hdet
  have hz0 : IsAlgebraic K (z 0) := by
    rw [eq_inv_of_mul_eq_one_left hinv]
    exact (algebraic_eval (JacobianKernelCharts.jacobian q) (fun i => z i.succ) ha).inv
  exact Fin.cases hz0 ha

theorem finite_extended [CharZero K] (q : Fin n → MvPolynomial (Fin n) K) :
    {z : Fin (n + 1) → K | ∀ j, aeval z (system q j) = 0}.Finite := by
  have hfin := FiniteAlgebraicZeros.finite_zeroSet (ideal q) (quotient_algebraic q)
  apply hfin.subset
  intro z hz
  have hk : ideal q ≤ RingHom.ker (aeval z).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hz j
  exact fun p hp => hk hp

theorem finite_regular_roots [CharZero K] (q : Fin n → MvPolynomial (Fin n) K) :
    {x : Fin n → K | (∀ j, aeval x (q j) = 0) ∧ aeval x (JacobianKernelCharts.jacobian q) ≠ 0}.Finite := by
  apply ((finite_extended q).image (fun z i => z i.succ)).subset
  rintro x ⟨hx, hdet⟩
  let z : Fin (n + 1) → K := Fin.cons ((aeval x (JacobianKernelCharts.jacobian q))⁻¹) x
  refine ⟨z, (system_iff q z).mpr ?_, ?_⟩
  · simpa only [z, Fin.cons_zero, Fin.cons_succ] using And.intro (inv_mul_cancel₀ hdet) hx
  · rfl

theorem finite_roots_of_regular [CharZero K] (q : Fin n → MvPolynomial (Fin n) K)
    (hreg : ∀ x : Fin n → K, (∀ j, aeval x (q j) = 0) → aeval x (JacobianKernelCharts.jacobian q) ≠ 0) :
    {x : Fin n → K | ∀ j, aeval x (q j) = 0}.Finite :=
  (finite_regular_roots q).subset (fun x hx => ⟨hx, hreg x hx⟩)

end LeanCanny.Algebra.SquareSystemFinite
