/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FermatSweepKernelCertificate
public import LeanCanny.ETR.ComplexCriticalKernelFinite

/-! # Connecting affine kernel circuits to the sampled sweep predicate

The source polynomial identity is explicit: its complex coefficient image is
the variable-renamed sampled Fermat polynomial. This single identity transfers
the value, gradient, and Hessian; no derivative evaluator is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FermatSweepCertificate
open MvPolynomial LeanCanny.Algebra LeanCanny.ETR.ComplexCircuit
open scoped Classical BigOperators

variable {n : ℕ}

noncomputable def sampledPolynomial (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ)
    (N : ℕ) (record : List Bool) : MvPolynomial (Fin (n + 1)) ℂ :=
  (FermatCriticalHomogenization.polynomial (FermatBoundedSweepSample.lower low a N) (Polynomial.C a) N).map
    (sampleMap n N record)

theorem finite_bad_iff_affine (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ)
    (N : ℕ) (record : List Bool) (v : ℕ → ℤ)
    (hv : ∀ j : Fin n, v j.val = (direction n N record j : ℤ)) (chart : Fin (n + 1)) :
    CriticalKernel.FiniteBad (sampledPolynomial low a N record) v chart ↔ AffineBad low a N record chart := by
  have ha := affine_bad_iff low a N record chart
  dsimp only at ha
  have hv' (j : Fin n) : (v j.val : ℂ) = (direction n N record j : ℂ) := by
    rw [hv j, Int.cast_natCast]
  exact (CriticalKernel.finite_bad_map_iff (sampleMap n N record)
    (FermatCriticalHomogenization.polynomial (FermatBoundedSweepSample.lower low a N) (Polynomial.C a) N)
    v (fun j => (direction n N record j : ℂ)) hv' chart).trans ha.symm

theorem kernel_query_correct (low : MvPolynomial (Fin (n + 2)) ℚ) (a : ℚ)
    (N : ℕ) (record : List Bool) (v : ℕ → ℤ)
    (hv : ∀ j : Fin n, v j.val = (direction n N record j : ℤ)) (chart : Fin (n + 1))
    (wire : ℕ → MvPolynomial ℕ ℤ) (start : ℕ) (ops : List Operation) (out : ℕ)
    (hw : StraightLine.WellFormed start ops) (hr : Differential.Realizes wire start ops)
    (hin : ∀ i < start, wire i = X i) (ho : out < start + ops.length)
    (hsource : (wire out).map (Int.castRingHom ℂ) = rename Fin.val (sampledPolynomial low a N record)) :
    Satisfiable (CriticalKernel.query start (n + 1) ops out v chart.val) ↔ AffineBad low a N record chart :=
  (CriticalKernel.query_satisfiable wire start (n + 1) ops out v chart.val chart.isLt hw hr hin ho).trans
    ((CriticalKernel.bad_iff_finite (wire out) _ hsource v chart).trans
      (finite_bad_iff_affine low a N record v hv chart))

end LeanCanny.Encoding.FermatSweepCertificate
