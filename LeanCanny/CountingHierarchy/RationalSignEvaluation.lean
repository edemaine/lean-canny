/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RationalSignProduct
public import LeanCanny.CountingHierarchy.IndexedPowerProduct

/-! # Counting-level evaluation of the integer sign-approximation product -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

@[expose] noncomputable def rationalSignProductResidue (p B s z : ℕ) : ℕ :=
  primeFieldProduct p (2 * B + 1).size (fun w =>
    let j := BitString.binaryValue w
    if j < 2 * B + 1 then
      powMod p ((powMod p 2 (j - B) + powMod p 2 (B - j) * z) % p) (2 * s)
    else 1)

/-- The dyadic product has a binary number of factors; Frontier's product
construction adds three levels to its uniformly accessible argument. -/
theorem rationalSignProductResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B s z : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hz : z ∈ CountingFunction a enc encNat) :
    (fun w => rationalSignProductResidue (p w) (B w) (s w) (z w)) ∈
      CountingFunction (a + 3) enc encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encBits)
  have hB' := hB.comp (ComputableInPolyTime.fst enc encBits)
  have hs' := hs.comp (ComputableInPolyTime.fst enc encBits)
  have hj : ComputableInPolyTime (fun q : α × List Bool => BitString.binaryValue q.2)
      (encPair enc encBits) encNat := by fun_prop
  have ha := computableInPolyTime_powMod hp' (.const 2)
    (ComputableInPolyTime.binary_sub' hj hB')
  have hb := computableInPolyTime_powMod hp' (.const 2)
    (ComputableInPolyTime.binary_sub' hB' hj)
  have hz' := CountingFunction.preprocess hz (ComputableInPolyTime.fst enc encBits)
  have hsum := CountingFunction.map (CountingFunction.prod (CountingFunction.of_polyTime ha)
    (CountingFunction.nat_mul (CountingFunction.of_polyTime hb) hz'))
    ComputableInPolyTime.binary_add
  have hpower := CountingFunction.powMod (CountingFunction.of_polyTime hp')
    (CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp'))
    (CountingFunction.of_polyTime (ComputableInPolyTime.binary_mul' (.const 2) hs'))
  have hcount := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (.const 2) hB) (.const 1)
  have htest : ComputableInPolyTime
      (fun q : α × List Bool => decide (BitString.binaryValue q.2 < 2 * B q.1 + 1))
      (encPair enc encBits) encBool := by fun_prop
  have hfactor := CountingFunction.ite (CountingFunction.of_polyTime htest) hpower
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1))
  simpa only [rationalSignProductResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.primeFieldProduct_mem E hfactor hp
      (ComputableInPolyTime.binary_size.comp hcount)

/-- The modular evaluator computes the actual integer polynomial, rather
than a formal oracle for its expanded coefficients. -/
theorem rationalSignProductResidue_cast {p : ℕ} [Fact p.Prime] (B s z : ℕ) :
    (rationalSignProductResidue p B s z : ZMod p) =
      (rationalSignProduct B s).eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  rw [rationalSignProductResidue, primeFieldProduct_spec]
  simp only [Nat.cast_ite, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  have h := BitString.sum_binaryValue_lt (M := Additive (ZMod p))
    (Nat.lt_size_self (2 * B + 1)).le
    (fun j => Additive.ofMul (((2 : ZMod p) ^ (j - B) +
      (2 : ZMod p) ^ (B - j) * z) ^ (2 * s)))
  have he : (∏ w : Fin (2 * B + 1).size → Bool,
      if BitString.binaryValue (List.ofFn w) < 2 * B + 1 then
        ((2 : ZMod p) ^ (BitString.binaryValue (List.ofFn w) - B) +
          2 ^ (B - BitString.binaryValue (List.ofFn w)) * z) ^ (2 * s)
      else 1) = ∏ j ∈ Finset.range (2 * B + 1),
        ((2 : ZMod p) ^ (j - B) + 2 ^ (B - j) * z) ^ (2 * s) :=
    congrArg Additive.toMul h
  rw [he, rationalSignProduct, Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]

end LeanCanny.CountingHierarchy
