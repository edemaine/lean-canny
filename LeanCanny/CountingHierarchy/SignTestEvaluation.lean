/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RationalSignEvaluation
public import LeanCanny.CountingHierarchy.ModularArithmetic
public import LeanCanny.CountingHierarchy.ClearedSignTests

/-! # Uniform residues of cleared sign-test numerators and denominators -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def signDenominatorResidue (p B s z : ℕ) : ℕ :=
  (rationalSignProductResidue p B s z +
    rationalSignProductResidue p B s (modularSub p 0 z)) % p

@[expose] noncomputable def signNumeratorResidue (p B s z : ℕ) : ℕ :=
  modularSub p (rationalSignProductResidue p B s z)
    (rationalSignProductResidue p B s (modularSub p 0 z))

theorem signTestResidues_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p B s z : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hB : ComputableInPolyTime B enc encNat)
    (hs : ComputableInPolyTime s enc encNat)
    (hz : z ∈ CountingFunction a enc encNat) :
    ((fun w => signDenominatorResidue (p w) (B w) (s w) (z w)) ∈
      CountingFunction (a + 3) enc encNat) ∧
    ((fun w => signNumeratorResidue (p w) (B w) (s w) (z w)) ∈
      CountingFunction (a + 3) enc encNat) := by
  have hneg := modularSub_mem (CountingFunction.of_polyTime hp)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 0)) hz
  have hpos := rationalSignProductResidue_mem E hp hB hs hz
  have hnegval := rationalSignProductResidue_mem E hp hB hs hneg
  constructor
  · exact CountingFunction.nat_mod
      (CountingFunction.map (CountingFunction.prod hpos hnegval) ComputableInPolyTime.binary_add)
      (CountingFunction.of_polyTime hp)
  · exact modularSub_mem (CountingFunction.of_polyTime hp) hpos hnegval

theorem signTestResidues_cast {p : ℕ} [Fact p.Prime] (B s z : ℕ)
    (g : Polynomial ℤ) (x : ZMod p)
    (hz : (z : ZMod p) = g.eval₂ (Int.castRingHom (ZMod p)) x) :
    (signDenominatorResidue p B s z : ZMod p) =
      (signTestDenominator B s g).eval₂ (Int.castRingHom (ZMod p)) x ∧
    (signNumeratorResidue p B s z : ZMod p) =
      (signTestNumerator B s g).eval₂ (Int.castRingHom (ZMod p)) x := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hn : (modularSub p 0 z : ZMod p) = -g.eval₂ (Int.castRingHom (ZMod p)) x := by
    rw [modularSub_cast hp, Nat.cast_zero, zero_sub, hz]
  constructor
  · rw [signDenominatorResidue, ZMod.natCast_mod, Nat.cast_add,
      rationalSignProductResidue_cast, rationalSignProductResidue_cast, hz, hn,
      signTestDenominator, Polynomial.eval₂_add, Polynomial.eval₂_comp,
      Polynomial.eval₂_comp, Polynomial.eval₂_neg]
  · rw [signNumeratorResidue, modularSub_cast hp,
      rationalSignProductResidue_cast, rationalSignProductResidue_cast, hz, hn,
      signTestNumerator, Polynomial.eval₂_sub, Polynomial.eval₂_comp,
      Polynomial.eval₂_comp, Polynomial.eval₂_neg]

end LeanCanny.CountingHierarchy
