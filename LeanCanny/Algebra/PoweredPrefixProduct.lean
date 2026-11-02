/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.TransformedRecursiveProduct
public import LeanCanny.Algebra.ImplicitPowerResidueFP

/-! # Stream a power of an old denominator product and one final coefficient

Each old leading residue is raised to the binary exponent locally. The last
charged residue is multiplied once. All processing is modulo the original
query modulus, including modulus one and composite moduli.
-/
@[expose] public section
namespace LeanCanny.Algebra.PoweredPrefixProduct
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def root (p : List Bool) := pairFst (pairFst p)

def exponentWord (count exponent : List Bool → ℕ) (p : List Bool) : List Bool :=
  BinaryNatCode.encode (if Nat.fromBitsLE (pairSnd (pairFst p)) < count (root p) then exponent (root p) else 1)

def transform (count exponent pred : List Bool → ℕ) : List Bool → List Bool :=
  ImplicitPowerResidue.value pairSnd (exponentWord count exponent)
    (fun p => BinaryNatCode.encode (pred (root p)))

theorem transform_FP (count exponent pred : List Bool → ℕ)
    (hc : BinaryFn count) (he : BinaryFn exponent) (hm : BinaryFn pred) : transform count exponent pred ∈ FP := by
  have HR : root ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HI : BinaryFn (fun p => Nat.fromBitsLE (pairSnd (pairFst p))) :=
    BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have HEX : BinaryFn (fun p => exponent (root p)) := he.comp HR
  have HMX : BinaryFn (fun p => pred (root p)) := hm.comp HR
  have HEXI : BinaryFn (fun p => if Nat.fromBitsLE (pairSnd (pairFst p)) < count (root p) then exponent (root p) else 1) :=
    BinaryFn.ite (HI.lt (hc.comp HR)) HEX (BinaryFn.const 1)
  have HE : exponentWord count exponent ∈ FP := HEXI.bits_mem_FP
  exact ImplicitPowerResidue.value_mem_FP _ _ _ pairSnd_mem_FP HE HMX.bits_mem_FP

theorem transform_packet (count exponent pred : List Bool → ℕ) (q : List Bool) (i : ℕ)
    (z : ZMod (pred q + 1)) :
    transform count exponent pred (pair (pair q (BinaryNatCode.encode i)) (residueBits z)) =
      residueBits (z ^ (if i < count q then exponent q else 1)) := by
  let : NeZero (pred q + 1) := ⟨by omega⟩
  unfold transform ImplicitPowerResidue.value
  rw [BinaryNat.powMod_eq_bits]
  simp only [root, exponentWord, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    residueBits, Nat.fromBitsLE_bits]
  let e := if i < count q then exponent q else 1
  have H : (z ^ e).val = z.val ^ e % (pred q + 1) := by
    calc
      _ = ((z.val : ZMod (pred q + 1)) ^ e).val := by rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [← Nat.cast_pow, ZMod.val_natCast]
  exact congrArg Nat.bits H.symm

def program (count exponent pred : List Bool → ℕ) (task : List Bool → List Bool) : RecursiveFold.Program :=
  TransformedRecursiveProduct.program (fun q => count q + 1)
    (fun q => BinaryNatCode.encode (pred q + 1)) task (transform count exponent pred)

theorem certificates (count exponent pred : List Bool → ℕ) (task : List Bool → List Bool)
    (hc : BinaryFn count) (he : BinaryFn exponent) (hm : BinaryFn pred) (ht : task ∈ FP) :
    (program count exponent pred task).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  TransformedRecursiveProduct.certificates _ _ _ _ (hc.add (BinaryFn.const 1))
    (hm.add (BinaryFn.const 1)).bits_mem_FP ht (transform_FP count exponent pred hc he hm)

private theorem program_value (count exponent pred : List Bool → ℕ) (task answer : List Bool → List Bool)
    (q : List Bool) :
    (program count exponent pred task).value answer q =
      (TransformedRecursiveProduct.program (fun q => count q + 1)
        (fun q => BinaryNatCode.encode (pred q + 1)) task (transform count exponent pred)).partialValue
        answer q (count q + 1) := rfl

attribute [local irreducible] program transform

theorem value (count exponent pred : List Bool → ℕ) (task answer : List Bool → List Bool)
    (q : List Bool) (a : ℕ → ZMod (pred q + 1)) (last : ZMod (pred q + 1))
    (ha : ∀ i < count q, answer (task (pair q (BinaryNatCode.encode i))) = residueBits (a i))
    (hlast : answer (task (pair q (BinaryNatCode.encode (count q)))) = residueBits last) :
    (program count exponent pred task).value answer q =
      residueBits ((∏ i ∈ Finset.range (count q), a i) ^ exponent q * last) := by
  rw [program_value]
  let b : ℕ → ZMod (pred q + 1) := fun i => if i < count q then a i ^ exponent q else last
  have HB (i : ℕ) (hi : i < count q + 1) :
      TransformedRecursiveProduct.mapped task (transform count exponent pred) answer
        (pair q (BinaryNatCode.encode i)) = residueBits (b i) := by
    unfold TransformedRecursiveProduct.mapped
    by_cases h : i < count q
    · rw [ha i h, transform_packet, ite_eq_left h]
      simp only [b, ite_eq_left h]
    · have H : i = count q := by omega
      subst i
      rw [hlast, transform_packet, ite_eq_right (Nat.lt_irrefl _), pow_one]
      simp only [b, ite_eq_right (Nat.lt_irrefl _)]
  have HV := TransformedRecursiveProduct.partialValueWithModulus (fun q => count q + 1)
    (fun q => BinaryNatCode.encode (pred q + 1)) task (transform count exponent pred) answer
    (fun q => pred q + 1) (funext fun r => Nat.fromBitsLE_bits _) q b (by omega) HB (count q + 1) le_rfl
  have Hprefix : (∏ i ∈ Finset.range (count q), b i) =
      (∏ i ∈ Finset.range (count q), a i) ^ exponent q := by
    calc
      _ = ∏ i ∈ Finset.range (count q), a i ^ exponent q :=
        Finset.prod_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi))
      _ = _ := Finset.prod_pow _ _ _
  have Hproduct : (∏ i ∈ Finset.range (count q + 1), b i) =
      (∏ i ∈ Finset.range (count q), a i) ^ exponent q * last := by
    rw [Finset.prod_range_succ, Hprefix]
    simp only [b, Nat.lt_irrefl, ite_false]
  exact HV.trans (congrArg (fun z : ZMod (pred q + 1) => residueBits z) Hproduct)

end LeanCanny.Algebra.PoweredPrefixProduct
