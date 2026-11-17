/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IntegerResidueFP
public import LeanCanny.ETR.TermView
public import LeanCanny.ETR.NNFEncoding
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # A bounded raw-data algebra for modular expression-tree evaluation

Raw arithmetic payloads remain intact while separate annotations evaluate
complete expression nodes. This prevents integer payloads from being mistaken
for arithmetic subexpressions during the bottom-up pass.
-/

@[expose] public section

namespace LeanCanny.CountingHierarchy.TermModular

open LeanCanny.Encoding LeanCanny.Algebra LeanCanny.ETR
open Brackets

 def modulus (p : ℕ) : ℕ := max 1 p

 def constant (p : ℕ) (payload : Data) : ℕ :=
  Nat.fromBitsLE (Codec.IntegerResidue.value (pair payload.toBits (BinaryNatCode.encode (modulus p)))) % modulus p

 def value (p : ℕ) (coordinate : ℕ → ℕ) : Data → ℕ
  | .l [tag, a] => if tag = Codec.unary 0 then constant p a
      else if tag = Codec.unary 1 then coordinate ((a.size - 2) / 2) % modulus p else 0
  | .l [tag, a, b] => if tag = Codec.unary 2 then (value p coordinate a + value p coordinate b) % modulus p
      else if tag = Codec.unary 3 then (value p coordinate a * value p coordinate b) % modulus p else 0
  | _ => 0

 theorem modulus_pos (p : ℕ) : 0 < modulus p := lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)

 theorem value_lt (p : ℕ) (coordinate : ℕ → ℕ) (d : Data) : value p coordinate d < modulus p := by
  cases d with
  | l xs =>
    rcases xs with _ | ⟨tag, _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩⟩
    all_goals simp only [value]
    all_goals (try split_ifs) <;> first | exact Nat.mod_lt _ (modulus_pos p) | exact modulus_pos p

 theorem constant_cast {p : ℕ} [Fact p.Prime] (z : ℤ) :
    (constant p (Codec.integer z) : ZMod p) = (z : ZMod p) := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : modulus p = p := max_eq_right (Fact.out : p.Prime).one_le
  rw [constant, hp, Codec.IntegerResidue.value_integer, MatrixPower.residueBits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.natCast_mod, ZMod.natCast_zmod_val]

 theorem value_term_cast {p : ℕ} [Fact p.Prime] (coordinate : ℕ → ℕ) (t : Term) :
    (value p coordinate t.toData : ZMod p) = t.eval (fun i => (coordinate i : ZMod p)) := by
  have hp : modulus p = p := max_eq_right (Fact.out : p.Prime).one_le
  induction t with
  | const z =>
    simpa only [Term.toData, value, ite_true, Term.eval] using constant_cast (p := p) z
  | var i =>
    have hi : ((Codec.unary i).size - 2) / 2 = i := by rw [Codec.unary_size]; omega
    have h10 : Codec.unary 1 ≠ Codec.unary 0 := by
      intro heq
      have hs := congrArg Data.size heq
      simp only [Codec.unary_size] at hs
      omega
    simp only [Term.toData, value, h10, ite_false, ite_true, hi, hp, ZMod.natCast_mod, Term.eval]
  | add t u ht hu =>
    simpa only [Term.toData, value, ite_true, hp, ZMod.natCast_mod, Nat.cast_add, Term.eval] using
      congrArg₂ (· + ·) ht hu
  | mul t u ht hu =>
    have h32 : Codec.unary 3 ≠ Codec.unary 2 := by
      intro heq
      have hs := congrArg Data.size heq
      simp only [Codec.unary_size] at hs
      omega
    simpa only [Term.toData, value, h32, ite_false, ite_true, hp,
      ZMod.natCast_mod, Nat.cast_mul, Term.eval] using congrArg₂ (· * ·) ht hu

end LeanCanny.CountingHierarchy.TermModular
