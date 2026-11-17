/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Factorial
public import LeanCanny.CountingHierarchy.GridEnumeration
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! # Uniform indexed products of modular powers -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

/-- Exponents are addressed in a short list. The total product evaluator
 pads the binary index domain with factors equal to one. -/
@[expose] noncomputable def indexedPowerProduct (p n : ℕ) (j : List ℕ)
    (value : ℕ → ℕ) : ℕ :=
  primeFieldProduct p n.size (fun w =>
    if BitString.binaryValue w < n then
      powMod p (value (BitString.binaryValue w)) (j[BitString.binaryValue w]?.getD 0)
    else 1)

theorem indexedPowerProduct_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n : α → ℕ} {j : α → List ℕ} {value : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hn : ComputableInPolyTime n enc encNat)
    (hj : ComputableInPolyTime j enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => indexedPowerProduct (p w) (n w) (j w) (fun i => value (w, i))) ∈
      CountingFunction (a + 3) enc encNat := by
  have hi : ComputableInPolyTime (fun q : α × List Bool => BitString.binaryValue q.2)
      (encPair enc encBits) encNat := by fun_prop
  have hp' := hp.comp (ComputableInPolyTime.fst enc encBits)
  have hn' := hn.comp (ComputableInPolyTime.fst enc encBits)
  have hj' := hj.comp (ComputableInPolyTime.fst enc encBits)
  have he : ComputableInPolyTime
      (fun q : α × List Bool => (j q.1)[BitString.binaryValue q.2]?.getD 0)
      (encPair enc encBits) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hj' hi
  have hvalue := CountingFunction.preprocess hv
    ((ComputableInPolyTime.fst enc encBits).prod hi)
  have hpower := CountingFunction.powMod (CountingFunction.of_polyTime hp') hvalue
    (CountingFunction.of_polyTime he)
  have htest := CountingFunction.nat_lt (a := a) (CountingFunction.of_polyTime hi)
    (CountingFunction.of_polyTime hn')
  have hfactor := CountingFunction.ite htest hpower
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1))
  simpa only [indexedPowerProduct, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.primeFieldProduct_mem E hfactor hp (ComputableInPolyTime.binary_size.comp hn)

theorem indexedPowerProduct_cast {p : ℕ} [Fact p.Prime] (n : ℕ) (j : List ℕ)
    (value : ℕ → ℕ) :
    (indexedPowerProduct p n j value : ZMod p) =
      ∏ i : Fin n, (value i.val : ZMod p) ^ (j[i.val]?.getD 0) := by
  rw [indexedPowerProduct, primeFieldProduct_spec]
  simp only [Nat.cast_ite, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one]
  have h := BitString.sum_binaryValue_lt (M := Additive (ZMod p)) (Nat.lt_size_self n).le
    (fun i => Additive.ofMul ((value i : ZMod p) ^ (j[i]?.getD 0)))
  have hp : (∏ w : Fin n.size → Bool,
      if BitString.binaryValue (List.ofFn w) < n then
        (value (BitString.binaryValue (List.ofFn w)) : ZMod p) ^
          (j[BitString.binaryValue (List.ofFn w)]?.getD 0) else 1) =
      ∏ i ∈ Finset.range n, (value i : ZMod p) ^ (j[i]?.getD 0) :=
    congrArg Additive.toMul h
  rw [Finset.prod_range] at hp
  exact hp

end LeanCanny.CountingHierarchy
