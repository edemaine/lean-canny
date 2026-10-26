/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullWriter
public import LeanCanny.ETR.BoundedRegularTerm
public import LeanCanny.Encoding.BinaryPowModFP

/-! # Native modular representatives of the bounded regular source

A coefficient query supplies a modulus predecessor. Binary modular powers
replace every large scalar before the polynomial-sized term is serialized.
The term represents the exact source after mapping its coefficients modulo
that positive modulus.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularModularTerm
open LeanCanny.ETR LeanCanny.Geometry LeanCanny.Algebra MvPolynomial BoundedFullWriter Brackets
open scoped Classical BigOperators

noncomputable def power (E : List Bool → ℕ) (modulus : List Bool → List Bool) (c : List Bool) : ℕ :=
  2 ^ E c % (Nat.fromBitsLE (modulus c) + 1)

theorem power_binary {E : List Bool → ℕ} {modulus : List Bool → List Bool}
    (hE : BinaryFn E) (hm : modulus ∈ FP) : BinaryFn (power E modulus) := by
  have hq := mem_FP_pair (constFn_mem_FP (BinaryNatCode.encode 2)) (mem_FP_pair hE.bits_mem_FP hm)
  have he := BinaryFn.fromBits (mem_FP_comp hq BinaryNat.powMod_mem_FP)
  apply he.of_eq
  intro c
  simp only [Function.comp_apply, BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, power]

noncomputable def term (P : Readers) (modulus : List Bool → List Bool) (c : List Bool) : Term :=
  BoundedRegularTerm.term (TermView.term (P.source c)) (P.dim c) (degree P c)
    (power (fun c => 2 * P.radius c) modulus c) (power (scaleExponent P) modulus c)
    (power (shiftExponent P) modulus c) (power (regularizationExponent P) modulus c)

theorem degree_unary {P : Readers} (h : P.PolyTime) : UnaryFn (degree P) :=
  (UnaryFn.const 2).mul (((UnaryFn.const 2).mul ((UnaryFn.const 2).mul ((size_unary h).add (UnaryFn.const 2)))).add
    (UnaryFn.const 1))

theorem encode_mem_FP {P : Readers} {modulus : List Bool → List Bool}
    (h : P.PolyTime) (hm : modulus ∈ FP) : (fun c => (term P modulus c).toData.toBits) ∈ FP := by
  have ht : (fun c => (TermView.term (P.source c)).toData.toBits) ∈ FP :=
    mem_FP_of_eq (mem_FP_comp h.source TermView.normalize_mem_FP) (fun c => TermView.normalize_eq_term _)
  exact BoundedRegularTerm.encode_mem_FP ht h.dim (degree_unary h)
    (power_binary ((BinaryFn.const 2).mul h.radius) hm) (power_binary (scaleExponent_binary h) hm)
    (power_binary (shiftExponent_binary h) hm) (power_binary (regularizationExponent_binary h) hm)

theorem power_cast (E : List Bool → ℕ) (modulus : List Bool → List Bool) (c : List Bool) :
    ((power E modulus c : ℕ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) =
      (2 : ZMod (Nat.fromBitsLE (modulus c) + 1)) ^ E c := by
  simp only [power, ZMod.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]

theorem polynomial_map (P : Readers) (modulus : List Bool → List Bool) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    ((term P modulus c).finitePolynomial (P.dim c + 4)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))) =
      (BoundedRegularSource.polynomial (original P c) (size P c) (size P c) (P.radius c)).map
        (Int.castRingHom (ZMod (Nat.fromBitsLE (modulus c) + 1))) := by
  have hpad : (TermView.term (P.source c)).finitePolynomial (P.dim c + 4) =
      rename (fun i : Fin (P.dim c) => (i.castAdd 2).castAdd 2) (original P c) := by
    rw [show original P c = (TermView.term (P.source c)).finitePolynomial (P.dim c) from rfl,
      ← Term.rename_finitePolynomial _ _ _ ht (show P.dim c ≤ P.dim c + 4 by omega)]
    congr 1
  rw [term, BoundedRegularTerm.finitePolynomial, hpad,
    BoundedRegularSource.polynomial, IntegerRegularSource.polynomial_eq]
  simp only [BoundedRegularSource.lower, BoundedZeroSource.polynomial, BoundedZeroSource.sphere,
    FermatCriticalHomogenization.polynomial, map_sub, map_add, map_mul, map_pow, map_sum,
    map_C, Int.coe_castRingHom, Int.cast_natCast, Int.cast_ofNat,
    IntegerRegularSource.scale,
    BoundedZeroSource.radiusSquared, rename_C, rename_X, rename_rename,
    power_cast, map_one, map_X, one_mul]
  rfl

end LeanCanny.Encoding.BoundedRegularModularTerm
