/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeBinaryNat
public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Encoding.BinaryModFP
public import LeanCanny.Encoding.BinaryPowModFP

/-! # Typed binary division and modular exponentiation

All natural inputs, intermediate values, and outputs use `encNat`. The
certificates compose the verified word routines, including their zero-divisor
conventions. Modular powers take binary exponents and a positive modulus;
the primitive uses a modulus predecessor, matching the total word protocol.

This layer imports the word algorithms; the base binary codec does not import
it, so clients of binary addition and subtraction need no division dependency.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime
open LeanCanny

/-- Binary quotient, including `a / 0 = 0`. -/
@[program_certificate]
theorem binary_div : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encNat encNat) encNat := by
  have ha := natBits_computable.comp (fst encNat encNat)
  have hm := natBits_computable.comp (snd encNat encNat)
  have h := fromBitsLE_computable.comp
    (Encoding.BinaryNat.div_mem_FP.comp (pair_computable ha hm))
  exact h.of_enc_eq fun p => by
    simp only [Function.comp_apply, Encoding.BinaryNat.div_pair, Nat.fromBitsLE_bits]

/-- Binary remainder, including `a % 0 = a`. -/
@[program_certificate]
theorem binary_mod : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encNat encNat) encNat := by
  have ha := natBits_computable.comp (fst encNat encNat)
  have hm := natBits_computable.comp (snd encNat encNat)
  have h := fromBitsLE_computable.comp
    (Encoding.BinaryNat.mod_mem_FP.comp (pair_computable ha hm))
  exact h.of_enc_eq fun p => by
    simp only [Function.comp_apply, Encoding.BinaryNat.mod_pair, Nat.fromBitsLE_bits]

/-- Both results stay binary, including when the divisor is zero. -/
@[program_certificate]
theorem binary_divMod :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
      (encPair encNat encNat) (encPair encNat encNat) := binary_div.prod binary_mod

@[program_certificate]
theorem binary_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a / right a) input encNat :=
  binary_div.comp (hleft.prod hright)

@[program_certificate]
theorem binary_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => left a % right a) input encNat :=
  binary_mod.comp (hleft.prod hright)

@[program_certificate]
theorem binary_divMod' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encNat)
    (hright : ComputableTidilyInPolyTime right input encNat) :
    ComputableTidilyInPolyTime (fun a => (left a / right a, left a % right a))
      input (encPair encNat encNat) := binary_divMod.comp (hleft.prod hright)

/-- Binary base and exponent, with the positive modulus specified by its predecessor. -/
@[program_certificate]
theorem binary_modPow :
    ComputableTidilyInPolyTime (fun p : ℕ × (ℕ × ℕ) => p.1 ^ p.2.1 % (p.2.2 + 1))
      (encPair encNat (encPair encNat encNat)) encNat := by
  have ha := natBits_computable.comp (fst encNat (encPair encNat encNat))
  have he := natBits_computable.comp ((snd encNat (encPair encNat encNat)).fst')
  have hm := natBits_computable.comp ((snd encNat (encPair encNat encNat)).snd')
  have h := fromBitsLE_computable.comp
    (Encoding.BinaryNat.powMod_mem_FP.comp (pair_computable ha (pair_computable he hm)))
  exact h.of_enc_eq fun p => by
    simp only [Function.comp_apply, Encoding.BinaryNat.powMod_eq_bits, pairFst_pair,
      pairSnd_pair, Nat.fromBitsLE_bits]

@[program_certificate]
theorem binary_modPowSucc' {α : Type} {input : α ↪ List Bool} {base exponent pred : α → ℕ}
    (hbase : ComputableTidilyInPolyTime base input encNat)
    (hexponent : ComputableTidilyInPolyTime exponent input encNat)
    (hpred : ComputableTidilyInPolyTime pred input encNat) :
    ComputableTidilyInPolyTime (fun a => base a ^ exponent a % (pred a + 1)) input encNat :=
  binary_modPow.comp (hbase.prod (hexponent.prod hpred))

/-- An actual modulus may be used when its positivity holds on every input. -/
@[program_certificate]
theorem binary_modPow' {α : Type} {input : α ↪ List Bool} {base exponent modulus : α → ℕ}
    (hbase : ComputableTidilyInPolyTime base input encNat)
    (hexponent : ComputableTidilyInPolyTime exponent input encNat)
    (hmodulus : ComputableTidilyInPolyTime modulus input encNat)
    (hpos : ∀ a, 0 < modulus a) :
    ComputableTidilyInPolyTime (fun a => base a ^ exponent a % modulus a) input encNat := by
  have h := binary_modPowSucc' hbase hexponent (binary_sub' hmodulus (const 1))
  exact h.of_enc_eq fun a => by
    simp only [Nat.sub_add_cancel (hpos a)]

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace LeanCanny
open Turing.MultiTapeTM

theorem BinaryFn.div {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z / g z) := ComputableTidilyInPolyTime.binary_div' hf hg

theorem BinaryFn.mod {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun z => f z % g z) := ComputableTidilyInPolyTime.binary_mod' hf hg

theorem BinaryFn.divMod {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    ComputableTidilyInPolyTime (fun z => (f z / g z, f z % g z))
      encBits (encPair encNat encNat) := ComputableTidilyInPolyTime.binary_divMod' hf hg

theorem BinaryFn.powModSucc {f e b : List Bool → ℕ}
    (hf : BinaryFn f) (he : BinaryFn e) (hb : BinaryFn b) :
    BinaryFn (fun z => f z ^ e z % (b z + 1)) :=
  ComputableTidilyInPolyTime.binary_modPowSucc' hf he hb

theorem BinaryFn.powMod {f e m : List Bool → ℕ}
    (hf : BinaryFn f) (he : BinaryFn e) (hm : BinaryFn m) (hpos : ∀ z, 0 < m z) :
    BinaryFn (fun z => f z ^ e z % m z) :=
  ComputableTidilyInPolyTime.binary_modPow' hf he hm hpos

end LeanCanny
