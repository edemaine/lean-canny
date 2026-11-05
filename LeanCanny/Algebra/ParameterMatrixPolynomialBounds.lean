/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ParameterMatrixMassBounds
public import LeanCanny.Algebra.ParameterNormalizationBounds
/-! # Parameter bounds for polynomial evaluation on an actual matrix

These bounds control the characteristic inverse used by leading normalization
without evaluating the retained parameter or constructing a field inverse.
-/
@[expose] public section
namespace LeanCanny.Algebra.ParameterMatrixPolynomialBounds
open Polynomial ParameterMatrixMassBounds
open scoped Classical BigOperators
variable {ι :Type*} [Fintype ι] [DecidableEq ι]

def evaluationBudget (n D H G :ℕ):=(D+1).size+G+D*(H+n.size)

theorem evaluationBudget_binary {n D H G :List Bool→ℕ}
    (hn :BinaryFn n) (hD :BinaryFn D) (hH :BinaryFn H) (hG :BinaryFn G):
    BinaryFn (fun q=>evaluationBudget (n q) (D q) (H q) (G q)):=
  ((hD.add (BinaryFn.const 1)).size.add hG).add (hD.mul (hH.add hn.size))

theorem inverseAt_degree {R :Type*} [CommRing R] (p :R[X]) (τ :ℕ):
    (IntegralParameterInverse.inverseAt p τ).natDegree≤p.natDegree:=by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [IntegralParameterInverse.coeff_inverseAt,coeff_eq_zero_of_natDegree_lt (by omega),neg_zero]

theorem aeval_mass (A :Matrix ι ι ℤ[X]) (q :(ℤ[X])[X]) (D H G :ℕ)
    (hDegree :q.natDegree≤D)
    (hA :∀i j,coefficientMass (A i j)≤2^H)
    (hQ :∀k,coefficientMass (q.coeff k)≤2^G) (i j :ι):
    coefficientMass (Polynomial.aeval A q i j)≤2^evaluationBudget (Fintype.card ι) D H G:=by
  rw [Polynomial.aeval_eq_sum_range' (by omega :q.natDegree<D+1)]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  calc
    _≤∑k∈Finset.range (D+1),coefficientMass (q.coeff k*(A^k) i j):=coefficientMass_sum_le _ _
    _≤∑_k∈Finset.range (D+1),2^G*2^(D*(H+(Fintype.card ι).size)):=by
      apply Finset.sum_le_sum
      intro k hk
      have HK :k≤D:=by have :=Finset.mem_range.mp hk;omega
      exact (coefficientMass_mul_le _ _).trans (Nat.mul_le_mul (hQ k)
        ((pow_mass A H hA k i j).trans (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_right _ HK))))
    _=(D+1)*(2^G*2^(D*(H+(Fintype.card ι).size))):=by simp
    _≤2^(D+1).size*(2^G*2^(D*(H+(Fintype.card ι).size))):=
      Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _=2^evaluationBudget (Fintype.card ι) D H G:=by
      rw [←pow_add,←pow_add]
      congr 1
      unfold evaluationBudget
      omega

theorem aeval_degree (A :Matrix ι ι ℤ[X]) (q :(ℤ[X])[X]) (D E F :ℕ)
    (hDegree :q.natDegree≤D) (hA :RelativeMatrixDegree.Bound A E)
    (hQ :∀k,(q.coeff k).natDegree≤F) (i j :ι):
    (Polynomial.aeval A q i j).natDegree≤F+D*E:=by
  rw [Polynomial.aeval_eq_sum_range' (by omega :q.natDegree<D+1)]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have HK :k≤D:=by have :=Finset.mem_range.mp hk;omega
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hQ k)
    ((RelativeMatrixDegree.pow hA k i j).trans (Nat.mul_le_mul_right E HK)))

end LeanCanny.Algebra.ParameterMatrixPolynomialBounds
