/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
public import Mathlib.Data.ZMod.Basic

/-! # Total modular subtraction preserving counting levels -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] def modularSub (p x y : ℕ) : ℕ := (x + (p - y % p)) % p

theorem modularSub_polyTime {α : Type} {enc : α ↪ List Bool} {p x y : α → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun w => modularSub (p w) (x w) (y w)) enc encNat :=
  ComputableInPolyTime.binary_mod.comp
    ((ComputableInPolyTime.binary_add' hx (ComputableInPolyTime.binary_sub' hp
      (ComputableInPolyTime.binary_mod.comp (hy.prod hp)))).prod hp)

theorem modularSub_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ} {p x y : α → ℕ}
    (hp : p ∈ CountingFunction a enc encNat)
    (hx : x ∈ CountingFunction a enc encNat)
    (hy : y ∈ CountingFunction a enc encNat) :
    (fun w => modularSub (p w) (x w) (y w)) ∈ CountingFunction a enc encNat := by
  have hsub := CountingFunction.map (CountingFunction.prod hp (CountingFunction.nat_mod hy hp))
    ComputableInPolyTime.binary_sub
  have hadd := CountingFunction.map (CountingFunction.prod hx hsub)
    ComputableInPolyTime.binary_add
  exact CountingFunction.nat_mod hadd hp

theorem modularSub_cast {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    (modularSub p x y : ZMod p) = (x : ZMod p) - (y : ZMod p) := by
  rw [modularSub, ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt _ hp).le,
    ZMod.natCast_self, ZMod.natCast_mod]
  ring

end LeanCanny.CountingHierarchy
