/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.GridEnumeration

/-!
# Uniform multivariate coefficient extraction at one counting level

The number of variables is unary, while the prime, address and coefficient
indices are binary. One sum over addresses below `p^n` extracts a coefficient
of a polynomial supplied through uniform modular evaluation access.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

/-- One total coefficient evaluator over a grid addressed by a single binary integer.
Missing coefficient indices default to zero, matching the point-list convention. -/
@[expose] noncomputable def multivariateCoefficientResidue
    (p n : ℕ) (β : List ℕ) (value : List ℕ → ℕ) : ℕ :=
  (powMod p (p - 1) n * ∑ r ∈ Finset.range (p ^ n),
    value (gridPoint p n r) * gridWeight p n β (gridPoint p n r)) % p

/-- Variable arity costs no additional counting depth: all coordinates are
handled by the polynomial-time address decoder and weight computation. -/
theorem multivariateCoefficientResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n : α → ℕ} {β : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encUnary)
    (hβ : ComputableInPolyTime β enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => multivariateCoefficientResidue (p w) (n w) (β w)
      (fun z => value (w, z))) ∈ CountingFunction (a + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hn' := hn.comp (ComputableInPolyTime.fst enc encNat)
  have hpoint := gridPoint_polyTime hp' hn' (ComputableInPolyTime.snd enc encNat)
  have hvalues := CountingFunction.preprocess (input := encPair enc encNat) hv
    (g := fun q : α × ℕ => (q.1, gridPoint (p q.1) (n q.1) q.2))
    ((ComputableInPolyTime.fst enc encNat).prod hpoint)
  have hweight := gridWeight_polyTime hp' hn'
    (hβ.comp (ComputableInPolyTime.fst enc encNat)) hpoint
  have hsum := CountingFunction.sum_range E
    (CountingFunction.nat_mul hvalues (CountingFunction.of_polyTime hweight))
    (ComputableInPolyTime.binary_pow' hp hn)
  have hsign := CountingFunction.powMod (a := a + 1) (CountingFunction.of_polyTime hp)
    (CountingFunction.of_polyTime (ComputableInPolyTime.binary_sub' hp (.const 1)))
    (CountingFunction.of_polyTime (ComputableInPolyTime.unary_to_binary.comp hn))
  exact CountingFunction.nat_mod (CountingFunction.nat_mul hsign hsum)
    (CountingFunction.of_polyTime hp)

/-- Correctness requires modular evaluation only at the addressed canonical points. -/
theorem multivariateCoefficientResidue_cast {p n : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (e : Fin n →₀ ℕ) (β : List ℕ)
    (value : List ℕ → ℕ) (hP : P.totalDegree < p - 1)
    (he : ∀ i, e i < p - 1) (hβ : ∀ i : Fin n, β[i.val]?.getD 0 = e i)
    (hvalue : ∀ r < p ^ n, (value (gridPoint p n r) : ZMod p) =
      MvPolynomial.eval
        (fun i : Fin n => (((gridPoint p n r)[i.val]?.getD 0 : ℕ) : ZMod p)) P) :
    (multivariateCoefficientResidue p n β value : ZMod p) = P.coeff e := by
  have hp : p.Prime := Fact.out
  rw [multivariateCoefficientResidue, ZMod.natCast_mod, Nat.cast_mul,
    powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow,
    Nat.cast_sub hp.one_lt.le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [Nat.cast_sum]
  have hterms :
      (∑ r ∈ Finset.range (p ^ n),
        ((value (gridPoint p n r) * gridWeight p n β (gridPoint p n r) : ℕ) : ZMod p)) =
      ∑ r ∈ Finset.range (p ^ n),
        MvPolynomial.eval
          (fun i : Fin n => (((gridPoint p n r)[i.val]?.getD 0 : ℕ) : ZMod p)) P *
          ∏ i : Fin n, (((gridPoint p n r)[i.val]?.getD 0 : ℕ) : ZMod p) ^
            (p - 1 - e i) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [Nat.cast_mul, hvalue r (Finset.mem_range.mp hr), gridWeight_cast]
    simp_rw [hβ]
  rw [hterms, sum_gridPoint (p := p) (n := n)
    (fun z : Fin n → ZMod p => MvPolynomial.eval z P * ∏ i, z i ^ (p - 1 - e i))]
  simpa only [ZMod.card] using (FiniteFieldCoefficients.mv_coeff_eq_sum P e
    (by simpa only [ZMod.card] using hP) (by simpa only [ZMod.card] using he)).symm

/-- The natural output is the canonical representative of the actual coefficient. -/
theorem multivariateCoefficientResidue_eq_val {p n : ℕ} [Fact p.Prime]
    (P : MvPolynomial (Fin n) (ZMod p)) (e : Fin n →₀ ℕ) (β : List ℕ)
    (value : List ℕ → ℕ) (hP : P.totalDegree < p - 1)
    (he : ∀ i, e i < p - 1) (hβ : ∀ i : Fin n, β[i.val]?.getD 0 = e i)
    (hvalue : ∀ r < p ^ n, (value (gridPoint p n r) : ZMod p) =
      MvPolynomial.eval
        (fun i : Fin n => (((gridPoint p n r)[i.val]?.getD 0 : ℕ) : ZMod p)) P) :
    multivariateCoefficientResidue p n β value = (P.coeff e).val := by
  have hlt : multivariateCoefficientResidue p n β value < p :=
    Nat.mod_lt _ (Fact.out : p.Prime).pos
  have h := congrArg ZMod.val
    (multivariateCoefficientResidue_cast P e β value hP he hβ hvalue)
  simpa only [ZMod.val_natCast_of_lt hlt] using h

end LeanCanny.CountingHierarchy
