/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiniteFieldCoefficients
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic

/-!
# One-counting-level coefficient extraction

The evaluator receives a modulus, coefficient index, and uniform polynomial
evaluation access. It sums weighted evaluations without expanding coefficients.
Its fixed-level certificate holds on every input; algebraic correctness requires
a prime exceeding the polynomial degree and the requested coefficient index by
at least two. Degrees and coefficient indices may have exponential value.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- Recover a natural coefficient residue by one finite-field Fourier sum.
The sum is a specification of a counting computation, not an explicit list
constructed by the deterministic realizing program. -/
@[expose] noncomputable def coefficientResidue (p k : ℕ) (value : ℕ → ℕ) : ℕ :=
  (p - ((∑ z ∈ Finset.range p, value z * powMod p z (p - 1 - k)) % p)) % p

/-- Uniform modular evaluations yield indexed coefficients at one higher
function level. Both the modulus and index use binary encodings. -/
theorem coefficientResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) {p k : α → ℕ} {value : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => coefficientResidue (p w) (k w) (fun z => value (w, z))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hk' := hk.comp (ComputableInPolyTime.fst enc encNat)
  have he := ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.binary_sub' hp' (.const 1)) hk'
  have hpower := CountingFunction.powMod (a := a) (CountingFunction.of_polyTime hp')
    (CountingFunction.of_polyTime (ComputableInPolyTime.snd enc encNat))
    (CountingFunction.of_polyTime he)
  have hsum := CountingFunction.sum_range D (CountingFunction.nat_mul hv hpower) hp
  have hmod := CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)
  have hsub := CountingFunction.map
    (CountingFunction.prod (CountingFunction.of_polyTime hp) hmod)
    ComputableInPolyTime.binary_sub
  exact CountingFunction.nat_mod hsub (CountingFunction.of_polyTime hp)

/-- The total evaluator represents the actual polynomial coefficient in the field.
Correctness uses values only on the canonical representatives below `p`. -/
theorem coefficientResidue_cast {p : ℕ} [Fact p.Prime]
    (P : Polynomial (ZMod p)) (k : ℕ) (value : ℕ → ℕ)
    (hP : P.natDegree < p - 1) (hk : k < p - 1)
    (hvalue : ∀ z < p, (value z : ZMod p) = P.eval (z : ZMod p)) :
    (coefficientResidue p k value : ZMod p) = P.coeff k := by
  have hp : p.Prime := Fact.out
  unfold coefficientResidue
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ hp.pos).le,
    ZMod.natCast_self, ZMod.natCast_mod, zero_sub]
  rw [FiniteFieldCoefficients.coeff_eq_neg_sum_range P k hP hk]
  congr 1
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [Nat.cast_mul, hvalue z (Finset.mem_range.mp hz),
    powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod, Nat.cast_pow]

/-- The returned natural is the canonical representative, including zero coefficients. -/
theorem coefficientResidue_eq_val {p : ℕ} [Fact p.Prime]
    (P : Polynomial (ZMod p)) (k : ℕ) (value : ℕ → ℕ)
    (hP : P.natDegree < p - 1) (hk : k < p - 1)
    (hvalue : ∀ z < p, (value z : ZMod p) = P.eval (z : ZMod p)) :
    coefficientResidue p k value = (P.coeff k).val := by
  have hlt : coefficientResidue p k value < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  have h := congrArg ZMod.val (coefficientResidue_cast P k value hP hk hvalue)
  simpa only [ZMod.val_natCast_of_lt hlt] using h

end LeanCanny.CountingHierarchy
