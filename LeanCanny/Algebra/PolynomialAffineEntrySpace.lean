/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PolynomialAffineDeformation
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Encoding.BinaryDivFP
public import LeanCanny.Computation.SpaceFunctionComposition

/-! # Complete coefficient access for an encoded affine polynomial entry

Queries are `pair context (pair row (pair column degree))`. Division by the
supplied radix separates the original parameter degree from the deformation
degree. One suspended original coefficient call and FP modular postprocessing
give the encoded affine entry, including the degree-zero diagonal contribution.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialAffineEntryBits
open Complexity LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets MatrixPower

def packet (c : List Bool) (r s d : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode r) (pair (BinaryNatCode.encode s) (BinaryNatCode.encode d)))

def row (q : List Bool) : List Bool := pairFst (pairSnd q)
def col (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def target (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))

theorem row_mem_FP : row ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem col_mem_FP : col ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem target_mem_FP : target ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def division (radix : List Bool → List Bool) (q : List Bool) : List Bool :=
  BinaryNat.divMod (pair (target q) (radix (pairFst q)))

def quotient (radix : List Bool → List Bool) : List Bool → List Bool := pairFst ∘ division radix
def remainder (radix : List Bool → List Bool) : List Bool → List Bool := pairSnd ∘ division radix

theorem division_mem_FP {radix : List Bool → List Bool} (hB : radix ∈ FP) : division radix ∈ FP :=
  mem_FP_comp (mem_FP_pair target_mem_FP (mem_FP_comp pairFst_mem_FP hB)) BinaryNat.divMod_mem_FP

theorem quotient_mem_FP {radix : List Bool → List Bool} (hB : radix ∈ FP) : quotient radix ∈ FP :=
  mem_FP_comp (division_mem_FP hB) pairFst_mem_FP

theorem remainder_mem_FP {radix : List Bool → List Bool} (hB : radix ∈ FP) : remainder radix ∈ FP :=
  mem_FP_comp (division_mem_FP hB) pairSnd_mem_FP

def originalInput (radix : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (row q) (pair (col q) (remainder radix q)))

theorem originalInput_mem_FP {radix : List Bool → List Bool} (hB : radix ∈ FP) : originalInput radix ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_pair row_mem_FP (mem_FP_pair col_mem_FP (remainder_mem_FP hB)))

theorem natEq_fppred {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    FPPred (fun q => Nat.fromBitsLE (f q) = Nat.fromBitsLE (g q)) :=
  ((BinaryNat.le_fppred hf hg).and (BinaryNat.le_fppred hg hf)).of_iff (fun _ => by omega)

def diagonal (modulus radix : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (row q) = Nat.fromBitsLE (col q) ∧ Nat.fromBitsLE (remainder radix q) = 0 then
    ArithmeticBits.one (modulus (pairFst q)) else []

theorem diagonal_mem_FP {modulus radix : List Bool → List Bool} (hm : modulus ∈ FP) (hB : radix ∈ FP) :
    diagonal modulus radix ∈ FP := by
  have hz : FPPred (fun q => Nat.fromBitsLE (remainder radix q) = 0) :=
    (natEq_fppred (remainder_mem_FP hB) (constFn_mem_FP [])).of_iff (fun _ => Iff.rfl)
  have ho := mem_FP_comp (mem_FP_comp pairFst_mem_FP hm) ArithmeticBits.one_mem_FP
  have h := ((natEq_fppred row_mem_FP col_mem_FP).and hz).ite_mem_FP ho (constFn_mem_FP [])
  exact mem_FP_of_eq (g := diagonal modulus radix) h (fun _ => by simp only [diagonal, Function.comp_apply])

def negative (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (modulus (pairFst (pairFst z))) (pairSnd z))

theorem negative_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : negative modulus ∈ FP := by
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm
  have h := mem_FP_comp (mem_FP_pair hmod pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq (g := negative modulus) h (fun _ => by simp only [negative, Function.comp_apply])

def linear (modulus radix : List Bool → List Bool) (z : List Bool) : List Bool :=
  ArithmeticBits.combine (pair (modulus (pairFst (pairFst z)))
    (pair (diagonal modulus radix (pairFst z)) (pair (negative modulus z) (ArithmeticBits.one (modulus (pairFst (pairFst z)))))))

theorem linear_mem_FP {modulus radix : List Bool → List Bool} (hm : modulus ∈ FP) (hB : radix ∈ FP) : linear modulus radix ∈ FP := by
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm
  have hd := mem_FP_comp pairFst_mem_FP (diagonal_mem_FP hm hB)
  have ho := mem_FP_comp hmod ArithmeticBits.one_mem_FP
  have h := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair hd (mem_FP_pair (negative_mem_FP hm) ho))) ArithmeticBits.combine_mem_FP
  exact mem_FP_of_eq (g := linear modulus radix) h (fun _ => by simp only [linear, Function.comp_apply])

def finish (modulus radix : List Bool → List Bool) (z : List Bool) : List Bool :=
  if BinaryNat.normalize (quotient radix (pairFst z)) = [] then pairSnd z
  else if BinaryNat.normalize (quotient radix (pairFst z)) = [true] then linear modulus radix z else []

theorem finish_mem_FP {modulus radix : List Bool → List Bool} (hm : modulus ∈ FP) (hB : radix ∈ FP) : finish modulus radix ∈ FP := by
  have hq := mem_FP_comp (mem_FP_comp pairFst_mem_FP (quotient_mem_FP hB)) BinaryNat.normalize_mem_FP
  have h1 := (stringEq_fppred hq (constFn_mem_FP [true])).ite_mem_FP (linear_mem_FP hm hB) (constFn_mem_FP [])
  have h := (stringEq_fppred hq (constFn_mem_FP [])).ite_mem_FP pairSnd_mem_FP h1
  exact mem_FP_of_eq (g := finish modulus radix) h (fun _ => by simp only [finish, Function.comp_apply])

def value (modulus radix reader : List Bool → List Bool) (q : List Bool) : List Bool :=
  finish modulus radix (pair q (reader (originalInput radix q)))

noncomputable def evaluator {reader modulus radix : List Bool → List Bool} (E : SpaceFunction reader)
    (hm : modulus ∈ FP) (hB : radix ∈ FP) : SpaceFunction (value modulus radix reader) := by
  have ES := ((E.precompose (originalInput radix) (originalInput_mem_FP hB)).withInput).postcompose
    (finish modulus radix) (finish_mem_FP hm hB)
  exact ES.congr (funext fun q => by simp only [value, Function.comp_apply])

theorem quotient_packet (radix : List Bool → List Bool) (c : List Bool) (r s d B : ℕ)
    (hB : radix c = BinaryNatCode.encode B) : quotient radix (packet c r s d) = BinaryNatCode.encode (d / B) := by
  simp only [quotient, division, Function.comp_apply, target, packet, pairFst_pair, pairSnd_pair, hB, BinaryNat.divMod_pair, MacaulayBits.fromBits_encode]
  rfl

theorem remainder_packet (radix : List Bool → List Bool) (c : List Bool) (r s d B : ℕ)
    (hB : radix c = BinaryNatCode.encode B) : remainder radix (packet c r s d) = BinaryNatCode.encode (d % B) := by
  simp only [remainder, division, Function.comp_apply, target, packet, pairFst_pair, pairSnd_pair, hB, BinaryNat.divMod_pair, MacaulayBits.fromBits_encode]
  rfl

theorem originalInput_packet (radix : List Bool → List Bool) (c : List Bool) (r s d B : ℕ)
    (hB : radix c = BinaryNatCode.encode B) : originalInput radix (packet c r s d) = packet c r s (d % B) := by
  rw [originalInput, remainder_packet radix c r s d B hB]
  simp only [row, col, packet, pairFst_pair, pairSnd_pair]

theorem context_packet (c : List Bool) (r s d : ℕ) : pairFst (packet c r s d) = c := by
  simp only [packet, pairFst_pair]

theorem diagonal_packet (modulus radix : List Bool → List Bool) (c : List Bool) (r s d m B : ℕ)
    (hm : modulus c = BinaryNatCode.encode m) (hB : radix c = BinaryNatCode.encode B) :
    diagonal modulus radix (packet c r s d) = residueBits
      (if d % B = 0 then (if r = s then (1 : ZMod m) else 0) else 0) := by
  rw [diagonal, remainder_packet radix c r s d B hB]
  simp only [row, col, packet, pairFst_pair, pairSnd_pair, hm, MacaulayBits.fromBits_encode]
  by_cases hd : d % B = 0
  · rw [ite_eq_left hd]
    by_cases hrs : r = s
    · rw [ite_eq_left ⟨hrs, hd⟩, ite_eq_left hrs]
      exact ArithmeticBits.one_residueBits m
    · rw [ite_eq_right (fun h => hrs h.1), ite_eq_right hrs]
      simp [residueBits, BinaryNatCode.encode]
  · rw [ite_eq_right (fun h => hd h.2), ite_eq_right hd]
    simp [residueBits, BinaryNatCode.encode]

theorem finish_packet (modulus radix : List Bool → List Bool) (c : List Bool) (r s d m B : ℕ)
    (hm : modulus c = BinaryNatCode.encode m) (hB : radix c = BinaryNatCode.encode B) (hpos : 0 < m) (x : ZMod m) :
    finish modulus radix (pair (packet c r s d) (residueBits x)) = residueBits
      (if d / B = 0 then x else if d / B = 1 then
        (if d % B = 0 then (if r = s then 1 else 0) else 0) - x else 0) := by
  let : NeZero m := ⟨hpos.ne'⟩
  simp only [finish, pairFst_pair, pairSnd_pair, quotient_packet radix c r s d B hB,
    BinaryNat.normalize_eq_bits, MacaulayBits.fromBits_encode, BinaryNat.bits_eq_nil_iff]
  by_cases h0 : d / B = 0
  · simp only [h0, ite_true]
  · have h1 : (d / B).bits = [true] ↔ d / B = 1 := by
      change BinaryNatCode.encode (d / B) = BinaryNatCode.encode 1 ↔ _
      exact BinaryNatCode.encode_injective.eq_iff
    simp only [h0, ite_false, h1]
    by_cases hd : d / B = 1
    · rw [ite_eq_left hd, ite_eq_left hd]
      simp only [linear, negative, pairFst_pair, pairSnd_pair, diagonal_packet modulus radix c r s d m B hm hB,
        context_packet, hm, ArithmeticBits.negate_residueBits, ArithmeticBits.one_residueBits, ArithmeticBits.combine_residueBits]
      congr 1
      ring
    · rw [ite_eq_right hd, ite_eq_right hd]
      simp [residueBits, BinaryNatCode.encode]

theorem value_packet (modulus radix reader : List Bool → List Bool) (c : List Bool) (r s d m B : ℕ)
    (hm : modulus c = BinaryNatCode.encode m) (hB : radix c = BinaryNatCode.encode B) (hmpos : 0 < m) (hBpos : 0 < B)
    (a : Polynomial (ZMod m)) (ha : a.natDegree < B)
    (hr : ∀ k, reader (packet c r s k) = residueBits (a.coeff k)) :
    value modulus radix reader (packet c r s d) =
      residueBits ((PolynomialKronecker.encode B (PolynomialAffineDeformation.affine a (if r = s then 1 else 0))).coeff d) := by
  rw [value, originalInput_packet radix c r s d B hB, hr, finish_packet modulus radix c r s d m B hm hB hmpos]
  rw [PolynomialAffineDeformation.encoded_coefficient a _ B d hBpos ha]

end LeanCanny.Algebra.PolynomialAffineEntryBits
