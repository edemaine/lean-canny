/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.NativeCriticalBounds
public import LeanCanny.CountingHierarchy.ModularArithmetic
public import LeanCanny.CountingHierarchy.RootLabelModularCorrectness
public import LeanCanny.CountingHierarchy.SeparatedCriticalValues

/-! # Native modular evaluation of the deformation parameter and potential -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped BigOperators

@[expose] def criticalParameterResidue (p n d b : ℕ) : ℕ :=
  powMod p 2 (criticalSpecializationExponent n d b)

@[expose] def criticalCutoffResidue (p n d b : ℕ) : ℕ :=
  powMod p 2 (criticalValueCutoffExponent (criticalValueMassExponent n d b))

@[expose] def criticalCenterResidue (p ell i : ℕ) : ℕ := powMod p (4 * ell) (i + 1)

@[expose] def criticalPotentialTermResidue (p ell i x : ℕ) : ℕ :=
  (modularSub p (powMod p x (ell + 1))
      ((ell + 1) * powMod p (criticalCenterResidue p ell i) ell * x) +
    (ell + 1) * powMod p (criticalCenterResidue p ell i) (ell + 1)) % p

@[expose] noncomputable def criticalPotentialResidue (p n ell : ℕ) (z : List ℕ) : ℕ :=
  unaryModularSum n (max 1 p) (fun i => criticalPotentialTermResidue p ell i (z[i]?.getD 0))

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem criticalParameterResidue_polyTime {p n d b : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalParameterResidue (p w) (n w) (d w) (b w)) enc encNat :=
  computableInPolyTime_powMod hp (.const 2) (criticalSpecializationExponent_polyTime hn hd hb)

@[fun_prop] theorem criticalCutoffResidue_polyTime {p n d b : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalCutoffResidue (p w) (n w) (d w) (b w)) enc encNat :=
  computableInPolyTime_powMod hp (.const 2)
    (ComputableInPolyTime.binary_add' (criticalValueMassExponent_polyTime hn hd hb) (.const 2))

@[fun_prop] theorem criticalCenterResidue_polyTime {p ell i : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hell : ComputableInPolyTime ell enc encNat)
    (hi : ComputableInPolyTime i enc encNat) :
    ComputableInPolyTime (fun w => criticalCenterResidue (p w) (ell w) (i w)) enc encNat :=
  computableInPolyTime_powMod hp (ComputableInPolyTime.binary_mul' (.const 4) hell)
    (ComputableInPolyTime.binary_add' hi (.const 1))

@[fun_prop] theorem criticalPotentialTermResidue_polyTime {p ell i x : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hell : ComputableInPolyTime ell enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun w => criticalPotentialTermResidue (p w) (ell w) (i w) (x w)) enc encNat := by
  have hcenter := criticalCenterResidue_polyTime hp hell hi
  have he := ComputableInPolyTime.binary_add' hell (.const 1)
  have hfirst := computableInPolyTime_powMod hp hx he
  have hlinear := ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_mul' he (computableInPolyTime_powMod hp hcenter hell)) hx
  have hlast := ComputableInPolyTime.binary_mul' he (computableInPolyTime_powMod hp hcenter he)
  exact ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_add' (modularSub_polyTime hp hfirst hlinear) hlast).prod hp)

theorem criticalPotentialResidue_mem {a : ℕ} {p n ell : α → ℕ} {z : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat)) :
    (fun w => criticalPotentialResidue (p w) (n w) (ell w) (z w)) ∈ CountingFunction a enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hx : ComputableInPolyTime (fun q : α × ℕ => (z q.1)[q.2]?.getD 0)
      (encPair enc encNat) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hz.comp hf) hi
  have ht := criticalPotentialTermResidue_polyTime (hp.comp hf) (hell.comp hf) hi hx
  simpa only [criticalPotentialResidue, Function.comp_apply] using
    unaryModularSum_mem hn (ComputableInPolyTime.binary_max' (.const 1) hp)
      (fun _ => lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) (CountingFunction.of_polyTime ht)

theorem criticalCenterResidue_cast {p : ℕ} [Fact p.Prime] (ell i : ℕ) :
    (criticalCenterResidue p ell i : ZMod p) = ((4 * ell : ℕ) : ZMod p) ^ (i + 1) := by
  rw [criticalCenterResidue, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero,
    ZMod.natCast_mod, Nat.cast_pow]

theorem criticalPotentialResidue_cast {p n : ℕ} [Fact p.Prime] (ell : ℕ) (z : List ℕ) :
    (criticalPotentialResidue p n ell z : ZMod p) =
      eval (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p))
        (potentialPolynomial ell (fun i : Fin n => ((separatedCenters ell i : ℕ) : ZMod p))) := by
  rw [criticalPotentialResidue, max_eq_right (Fact.out : p.Prime).one_le, unaryModularSum_cast,
    potentialPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [criticalPotentialTermResidue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    Nat.cast_one, powMod_of_ne_zero (Fact.out : p.Prime).ne_zero, Nat.cast_pow,
    modularSub_cast (Fact.out : p.Prime).pos, criticalCenterResidue_cast,
    map_add, map_sub, map_mul, map_pow, eval_X, eval_C, separatedCenters]

end LeanCanny.CountingHierarchy
