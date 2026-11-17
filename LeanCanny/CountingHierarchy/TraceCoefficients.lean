/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.TraceExponential
import CslibFrontier.Foundations.FieldTheory.Finite.Basic

/-!
# Indexed exponential coefficients from uniform trace residues

The logarithm slots are `-t_k/k`, with slot zero fixed to zero. All modular
divisions are implemented by powering, and out-of-range coefficient indices
return zero. The resulting coefficient algorithm has a conservative `F_(a+8)`
bound when the supplied trace residues lie in `F_(a+2)`.

Correctness identifies the result with the explicit truncated-exponential
polynomial. The Newton identity relating that polynomial to a matrix, and the
trace-residue evaluator for the pure-power quotient, remain separate obligations.
No characteristic-coefficient or matrix oracle is assumed here.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- The zero logarithm slot is masked before Fermat inversion, including at p=2. -/
@[expose] def traceLogarithmResidue (p k t : ℕ) : ℕ :=
  if k = 0 then 0 else (p - (t * powMod p k (p - 2) % p)) % p

private theorem traceLogarithmResidue_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => traceLogarithmResidue q.1 q.2.1 q.2.2)
      encNat3 encNat := by
  have hp : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => q.1) encNat3 encNat := by fun_prop
  have hk : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => q.2.1) encNat3 encNat := by fun_prop
  have ht : ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => q.2.2) encNat3 encNat := by fun_prop
  have hpower := computableInPolyTime_powMod hp hk
    (ComputableInPolyTime.binary_sub' hp (.const 2))
  have hmul := ComputableInPolyTime.binary_mul' ht hpower
  have hmod := ComputableInPolyTime.binary_mod.comp (hmul.prod hp)
  have hsub := ComputableInPolyTime.binary_sub' hp hmod
  have hres := ComputableInPolyTime.binary_mod.comp (hsub.prod hp)
  have hzero : ComputableInPolyTime
      (fun q : ℕ × ℕ × ℕ => decide (q.2.1 = 0)) encNat3 encBool := by fun_prop
  simpa only [traceLogarithmResidue, decide_eq_true_eq, Function.comp_apply] using
    ComputableInPolyTime.ite' hzero (ComputableInPolyTime.const 0) hres

theorem traceLogarithmResidue_cast {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : k < p) (t : ℕ) :
    (traceLogarithmResidue p k t : ZMod p) = -(t : ZMod p) / (k : ZMod p) := by
  have hp : p.Prime := Fact.out
  by_cases hk0 : k = 0
  · simp [traceLogarithmResidue, hk0]
  · have hkcast : (k : ZMod p) ≠ 0 := by
      intro hz
      have hd := (ZMod.natCast_eq_zero_iff k p).mp hz
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd
      omega
    rw [traceLogarithmResidue, ite_eq_right hk0, ZMod.natCast_mod,
      Nat.cast_sub (Nat.mod_lt _ hp.pos).le, ZMod.natCast_self, ZMod.natCast_mod,
      zero_sub, Nat.cast_mul, powMod_of_ne_zero hp.ne_zero, ZMod.natCast_mod,
      Nat.cast_pow, ZMod.pow_card_sub_two_eq_inv hkcast]
    simp only [div_eq_mul_inv, neg_mul]

/-- The addressed reversed coefficient, with a total zero default above the dimension. -/
@[expose] noncomputable def traceExponentialCoefficient (p D d : ℕ) (t : ℕ → ℕ) : ℕ :=
  if d ≤ D then truncatedExponentialCoefficient p D (D - d)
    (fun k => traceLogarithmResidue p k (t k)) else 0

/-- The reconstructed expression is exactly the one with coefficients `-t_k/k`. -/
theorem traceExponentialCoefficient_eq {p : ℕ} [Fact p.Prime] {D d : ℕ}
    (hD : D < p - 1) (hdegree : D * D < p - 1) (hd : d ≤ D) (t : ℕ → ℕ) :
    traceExponentialCoefficient p D d t =
      ((truncatedExponential D (fun k => -(t k : ZMod p) / (k : ZMod p))).coeff
        (D - d)).val := by
  have hpoly : coefficientPolynomial D
      (fun k => (traceLogarithmResidue p k (t k) : ZMod p)) =
        coefficientPolynomial D (fun k => -(t k : ZMod p) / (k : ZMod p)) := by
    unfold coefficientPolynomial
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [traceLogarithmResidue_cast (p := p) (k := k)
      (by have := Finset.mem_range.mp hk; omega) (t k)]
  rw [traceExponentialCoefficient, ite_eq_left hd,
    truncatedExponentialCoefficient_eq (by omega) hdegree ((Nat.sub_le D d).trans_lt hD)]
  simp only [truncatedExponential, hpoly]

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- Forming the divided negative trace costs no additional counting level. -/
theorem traceLogarithmResidue_mem {p k t : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (ht : t ∈ CountingFunction a enc encNat) :
    (fun w => traceLogarithmResidue (p w) (k w) (t w)) ∈ CountingFunction a enc encNat :=
  CountingFunction.map
    (CountingFunction.prod (CountingFunction.of_polyTime hp)
      (CountingFunction.prod (CountingFunction.of_polyTime hk) ht)) traceLogarithmResidue_polyTime

/-- The trace-to-exponential-coefficient stage has fixed depth for binary dimensions. -/
theorem traceExponentialCoefficient_mem (E : Decoder enc) {p D d : α → ℕ}
    {t : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (ht : t ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => traceExponentialCoefficient (p w) (D w) (d w) (fun k => t (w, k))) ∈
      CountingFunction (max (a + 1) 3 + 2) enc encNat := by
  have hlog := traceLogarithmResidue_mem
    (hp.comp (ComputableInPolyTime.fst enc encNat)) (ComputableInPolyTime.snd enc encNat) ht
  have hc := truncatedExponentialCoefficient_mem E hp hD
    (ComputableInPolyTime.binary_sub' hD hd) hlog
  have hguard : ComputableInPolyTime
      (fun w => decide (d w ≤ D w)) enc encBool := by fun_prop
  simpa only [traceExponentialCoefficient, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite (CountingFunction.of_polyTime hguard) hc
      (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))

/-- An F_(a+2) trace evaluator fits the preprint's conservative F_(a+8) coefficient budget.
This is a certificate for the explicit exponential expression; matrix identification
and the supplied trace evaluator are not conclusions of this theorem. -/
theorem traceExponentialCoefficient_mem_eight (E : Decoder enc) {p D d : α → ℕ}
    {t : α × ℕ → ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (ht : t ∈ CountingFunction (a + 2) (encPair enc encNat) encNat) :
    (fun w => traceExponentialCoefficient (p w) (D w) (d w) (fun k => t (w, k))) ∈
      CountingFunction (a + 8) enc encNat :=
  CountingFunction.mono (by omega) (traceExponentialCoefficient_mem E hp hD hd ht)

end LeanCanny.CountingHierarchy
