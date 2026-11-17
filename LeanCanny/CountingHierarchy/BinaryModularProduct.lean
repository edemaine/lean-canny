/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.IndexedPowerProduct

/-! # Binary-length indexed prime-field products -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped BigOperators

noncomputable def binaryModularProduct (p n : ℕ) (value : ℕ → ℕ) : ℕ :=
  primeFieldProduct p n.size (fun w =>
    if BitString.binaryValue w < n then value (BitString.binaryValue w) else 1)

/-- The number of factors is binary. One uniform factor evaluator suffices,
and the cost is independent of the number of factors. -/
theorem binaryModularProduct_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n : α → ℕ} {value : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => binaryModularProduct (p w) (n w) (fun i => value (w, i))) ∈
      CountingFunction (a + 3) enc encNat := by
  have hi : ComputableInPolyTime (fun q : α × List Bool => BitString.binaryValue q.2)
      (encPair enc encBits) encNat := by fun_prop
  have hn' := hn.comp (ComputableInPolyTime.fst enc encBits)
  have hvalue := CountingFunction.preprocess hv ((ComputableInPolyTime.fst enc encBits).prod hi)
  have htest := CountingFunction.nat_lt (a := a) (CountingFunction.of_polyTime hi) (CountingFunction.of_polyTime hn')
  have hfactor := CountingFunction.ite htest hvalue (CountingFunction.of_polyTime (ComputableInPolyTime.const 1))
  simpa only [binaryModularProduct, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.primeFieldProduct_mem E hfactor hp (ComputableInPolyTime.binary_size.comp hn)

theorem binaryModularProduct_cast {p : ℕ} [Fact p.Prime] (n : ℕ) (value : ℕ → ℕ) :
    (binaryModularProduct p n value : ZMod p) = ∏ i : Fin n, (value i.val : ZMod p) := by
  rw [binaryModularProduct, primeFieldProduct_spec]
  simp only [Nat.cast_ite, Nat.cast_one]
  have h := BitString.sum_binaryValue_lt (M := Additive (ZMod p)) (Nat.lt_size_self n).le
    (fun i => Additive.ofMul (value i : ZMod p))
  have he : (∏ w : Fin n.size → Bool,
      if BitString.binaryValue (List.ofFn w) < n then (value (BitString.binaryValue (List.ofFn w)) : ZMod p) else 1) =
      ∏ i ∈ Finset.range n, (value i : ZMod p) := congrArg Additive.toMul h
  rw [Finset.prod_range] at he
  exact he

end LeanCanny.CountingHierarchy
