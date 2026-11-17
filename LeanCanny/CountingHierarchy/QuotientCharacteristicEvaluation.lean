/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientTraceEvaluation
public import LeanCanny.CountingHierarchy.CharacteristicCoefficientEvaluation
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # Characteristic coefficients without constructing quotient matrices -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue
open scoped Classical

/-- The entire trace-to-characteristic computation uses only polynomial
 evaluations and short binary indices. -/
@[expose] noncomputable def quotientCharacteristicValue (p n ell B m : ℕ)
    (v J : List ℕ → ℕ) (r : ℕ → List ℕ → ℕ) : ℕ :=
  traceExponentialCoefficient p (ell ^ n) m (fun k => quotientTraceValue p n ell B k v J r)

/-- Uniform polynomial evaluations in `F_a` give actual quotient
 characteristic coefficients in `F_(a+8)`, without a trace oracle. -/
theorem quotientCharacteristicValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell B m : α → ℕ}
    {v J : α × List ℕ → ℕ} {r : α × (ℕ × List ℕ) → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hm : ComputableInPolyTime m enc encNat)
    (hv : v ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hJ : J ∈ CountingFunction a (encPair enc (encList encNat)) encNat)
    (hr : r ∈ CountingFunction a (encPair enc (encPair encNat (encList encNat))) encNat) :
    (fun w => quotientCharacteristicValue (p w) (n w) (ell w) (B w) (m w)
      (fun z => v (w, z)) (fun z => J (w, z)) (fun i z => r (w, i, z))) ∈
        CountingFunction (a + 8) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hn' := hn.comp (ComputableInPolyTime.fst enc encNat)
  have hell' := hell.comp (ComputableInPolyTime.fst enc encNat)
  have hB' := hB.comp (ComputableInPolyTime.fst enc encNat)
  have hv' : (fun q : (α × ℕ) × List ℕ => v (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encList encNat)) encNat :=
    CountingFunction.preprocess hv (by fun_prop)
  have hJ' : (fun q : (α × ℕ) × List ℕ => J (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encList encNat)) encNat :=
    CountingFunction.preprocess hJ (by fun_prop)
  have hr' : (fun q : (α × ℕ) × (ℕ × List ℕ) => r (q.1.1, q.2)) ∈
      CountingFunction a (encPair (encPair enc encNat) (encPair encNat (encList encNat))) encNat :=
    CountingFunction.preprocess hr (by fun_prop)
  have ht : (fun q : α × ℕ => quotientTraceValue (p q.1) (n q.1) (ell q.1) (B q.1) q.2
      (fun z => v (q.1, z)) (fun z => J (q.1, z)) (fun i z => r (q.1, i, z))) ∈
        CountingFunction (a + 5) (encPair enc encNat) encNat := by
    simpa only [Function.comp_apply] using
      quotientTraceValue_mem (Decoder.pair E Decoder.nat) hp' hn' hell' hB'
        (ComputableInPolyTime.snd enc encNat) hv' hJ' hr'
  have hc := traceExponentialCoefficient_mem (a := a + 5) E hp
    (ComputableInPolyTime.binary_pow' hell hn) hm ht
  simpa only [quotientCharacteristicValue] using
    CountingFunction.mono (b := a + 8) (by omega) hc

/-- A short numerator-degree bound follows from the ordinary degree bound
 on the objective and the small Jacobian matrix. -/
theorem quotient_trace_numerator_degree {S : Type*} [CommRing S] {n : ℕ}
    (d : ℕ) (r : Fin n → MvPolynomial (Fin n) S)
    (hr : ∀ i, (r i).totalDegree ≤ d) (v : MvPolynomial (Fin n) S)
    (Ω D k : ℕ) (hv : v.totalDegree ≤ Ω) (hk : k ≤ D) :
    (v ^ k * jacobian (d + 1) r).totalDegree ≤ D * Ω + n * d := by
  have hJ : (jacobian (d + 1) r).totalDegree ≤ n * d := by
    apply polynomial_det_degree_le _ d
    intro i j
    have hX : (X i ^ (d + 1) : MvPolynomial (Fin n) S).totalDegree ≤ d + 1 := by
      rw [X_pow_eq_monomial]
      exact (totalDegree_monomial_le _ _).trans (by
        change (Finsupp.single i (d + 1)).degree ≤ d + 1
        rw [Finsupp.degree_single])
    have hf := (totalDegree_sub _ _).trans (max_le hX ((hr i).trans (Nat.le_succ d)))
    exact (LeanCanny.Algebra.PartialDerivativeDegree.degree_le _ j).trans (by omega)
  apply (totalDegree_mul _ _).trans
  apply Nat.add_le_add _ hJ
  exact (totalDegree_pow v k).trans (Nat.mul_le_mul hk hv)

/-- Correctness of the constructed evaluator for the actual normal-basis
 multiplication matrix. The cutoff and degree conditions concern only short
 bounds; no expanded characteristic polynomial is queried. -/
theorem quotientCharacteristicValue_eq {p n B m : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) (ZMod p)) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) (ZMod p))
    (hdeg : ∀ k ≤ (d + 1) ^ n, (v ^ k * jacobian (d + 1) r).totalDegree ≤ B)
    (hcut : (d + 1) * (B + 1) + 1 < p)
    (hD : (d + 1) ^ n < p - 1) (hdegree : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value Jvalue : List ℕ → ℕ) (rvalue : ℕ → List ℕ → ℕ)
    (hvalue : ∀ s < p ^ n, (value (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) v)
    (hJvalue : ∀ s < p ^ n, (Jvalue (gridPoint p n s) : ZMod p) =
      eval (fun i : Fin n => (((gridPoint p n s)[i.val]?.getD 0 : ℕ) : ZMod p)) (jacobian (d + 1) r))
    (hrvalue : ∀ i : Fin n, ∀ s < p ^ n, (rvalue i.val (gridPoint p n s) : ZMod p) =
      eval (fun j : Fin n => (((gridPoint p n s)[j.val]?.getD 0 : ℕ) : ZMod p)) (r i)) :
    quotientCharacteristicValue p n (d + 1) B m value Jvalue rvalue =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
        (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly.coeff m).val := by
  have hdim : Fintype.card (NormalIndex n (d + 1)) = (d + 1) ^ n := card_normalIndex _ _
  have h := traceExponentialCoefficient_eq_charpoly
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v)
    (by simpa only [hdim] using hD) (by simpa only [hdim] using hdegree) m
    (fun k => quotientTraceValue p n (d + 1) B k value Jvalue rvalue) (by
      intro k hk
      exact quotientTraceValue_cast d hd r hr v (hdeg k (by simpa only [hdim] using hk))
        hcut value Jvalue rvalue hvalue hJvalue hrvalue)
  simpa only [quotientCharacteristicValue, hdim] using h

end LeanCanny.CountingHierarchy
