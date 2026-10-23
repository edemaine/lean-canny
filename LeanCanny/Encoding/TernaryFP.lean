/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeBinaryArithmetic
public import Mathlib.Algebra.BigOperators.Fin

/-! # Polynomial-time ternary counts and digit access

The dimension is polynomially bounded, expressed by a unary FP certificate.
The query number and indices remain binary. A modulus with 2*k+1 bits bounds
every needed power of three, avoiding any unbounded integer exponentiation.
-/

@[expose] public section

namespace LeanCanny.Encoding.Ternary


theorem ones_value (n : ℕ) : Nat.fromBitsLE (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, Nat.fromBitsLE_cons, ↓reduceIte, pow_succ]
    omega

theorem power_lt (n k : ℕ) (hn : n ≤ k) : 3 ^ n < 2 ^ (2 * k + 1) := by
  have h1 : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by decide) _
  have h2 : 4 ^ n ≤ 4 ^ k := Nat.pow_le_pow_right (by decide) hn
  have he : 4 ^ k = 2 ^ (2 * k) := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, pow_mul]
  have hp : 0 < 2 ^ (2 * k) := pow_pos (by decide) _
  rw [he] at h2
  rw [pow_succ]
  omega

def padding (k : List Bool) : List Bool := List.replicate (2 * Nat.fromBitsLE k + 1) true
def power (k n : List Bool) : List Bool :=
  BinaryNat.powMod (pair (BinaryNatCode.encode 3) (pair n (padding k)))

theorem power_eq (k n : List Bool) (hn : Nat.fromBitsLE n ≤ Nat.fromBitsLE k) :
    power k n = BinaryNatCode.encode (3 ^ Nat.fromBitsLE n) := by
  simp only [power, BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, padding, ones_value]
  rw [Nat.mod_eq_of_lt (power_lt _ _ hn)]

theorem padding_mem_FP {k : List Bool → List Bool} (hk : UnaryFn (fun c => Nat.fromBitsLE (k c))) :
    (fun c => padding (k c)) ∈ FP := by
  have hw := ((hk.add hk).add (UnaryFn.const 1)).of_eq (g := fun c => 2 * Nat.fromBitsLE (k c) + 1)
    (fun c => by omega)
  exact hw.replicate_mem_FP true

theorem power_mem_FP {k n : List Bool → List Bool}
    (hk : UnaryFn (fun c => Nat.fromBitsLE (k c))) (hn : n ∈ FP) :
    (fun c => power (k c) (n c)) ∈ FP := by
  have h := (BinaryFn.const 3).powModSucc (BinaryFn.fromBits hn)
    (BinaryFn.fromBits (padding_mem_FP hk))
  refine mem_FP_of_eq h.bits_mem_FP ?_
  intro c
  simp only [power, BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

/-- The unreduced power certificate requires the same bound as `power_eq`. -/
theorem power_binary {k n : List Bool → List Bool}
    (hk : UnaryFn (fun c => Nat.fromBitsLE (k c))) (hn : n ∈ FP)
    (hbound : ∀ c, Nat.fromBitsLE (n c) ≤ Nat.fromBitsLE (k c)) :
    BinaryFn (fun c => 3 ^ Nat.fromBitsLE (n c)) :=
  BinaryFn.of_bits (mem_FP_of_eq (power_mem_FP hk hn) (fun c => power_eq _ _ (hbound c)))

def count (k : List Bool) : List Bool := power k k

theorem count_eq (k : List Bool) : count k = BinaryNatCode.encode (3 ^ Nat.fromBitsLE k) := power_eq _ _ le_rfl

theorem count_mem_FP {k : List Bool → List Bool} (hk : k ∈ FP)
    (hu : UnaryFn (fun c => Nat.fromBitsLE (k c))) : (fun c => count (k c)) ∈ FP := by
  refine mem_FP_of_eq (power_binary hu hk (fun _ => le_rfl)).bits_mem_FP ?_
  intro c
  exact (count_eq (k c)).symm

def digit (k q i : List Bool) : List Bool :=
  if Nat.fromBitsLE i < Nat.fromBitsLE k then
    BinaryNat.mod (pair (BinaryNat.div (pair q (power k i))) (BinaryNatCode.encode 3))
  else []

theorem digit_eq (k q i : List Bool) (hi : Nat.fromBitsLE i < Nat.fromBitsLE k) :
    digit k q i = BinaryNatCode.encode (Nat.fromBitsLE q / 3 ^ Nat.fromBitsLE i % 3) := by
  rw [digit, ite_eq_left hi, power_eq _ _ hi.le]
  simp only [BinaryNat.div_pair, BinaryNat.mod_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem digit_mem_FP {k q i : List Bool → List Bool} (hk : k ∈ FP) (hq : q ∈ FP) (hi : i ∈ FP)
    (hu : UnaryFn (fun c => Nat.fromBitsLE (k c))) : (fun c => digit (k c) (q c) (i c)) ∈ FP := by
  have hp := BinaryFn.fromBits (power_mem_FP hu hi)
  have hd := (BinaryFn.fromBits hq).div hp
  have hm := hd.mod (BinaryFn.const 3)
  have h := ((BinaryFn.fromBits hi).lt (BinaryFn.fromBits hk)).ite_mem_FP hm.bits_mem_FP (constFn_mem_FP [])
  refine mem_FP_of_eq h ?_
  intro c
  simp only [digit, BinaryNat.mod_pair, BinaryNat.div_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

def vector (k q : ℕ) (i : Fin k) : Fin 3 := ⟨q / 3 ^ i.val % 3, Nat.mod_lt _ (by decide)⟩

def exponent (k q i : ℕ) : Fin 3 :=
  if i < k then ⟨q / 3 ^ i % 3, Nat.mod_lt _ (by decide)⟩ else 0

theorem digit_exponent (k q i : List Bool) : digit k q i =
    BinaryNatCode.encode (exponent (Nat.fromBitsLE k) (Nat.fromBitsLE q) (Nat.fromBitsLE i)).val := by
  by_cases hi : Nat.fromBitsLE i < Nat.fromBitsLE k
  · rw [digit_eq _ _ _ hi]
    simp only [exponent, hi, ↓reduceIte]
  · simp only [digit, exponent, hi, ↓reduceIte]
    rfl

theorem exponent_fin (k q : ℕ) (i : Fin k) : exponent k q i.val = vector k q i := by
  simp only [exponent, i.isLt, ↓reduceIte, vector]

theorem vector_eq_symm (k : ℕ) (q : Fin (3 ^ k)) :
    vector k q.val = (finFunctionFinEquiv (m := 3) (n := k)).symm q := by
  funext i
  apply Fin.ext
  rfl

end LeanCanny.Encoding.Ternary
