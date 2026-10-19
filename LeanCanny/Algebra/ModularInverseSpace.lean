/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Encoding.BinaryPowModFP
public import Mathlib.Data.ZMod.Basic

/-!
# A space-bounded modular inverse search

Input `pair a (m-1)` uses a positive modulus. Scan candidates below `m`, retaining
the last candidate whose product with `a` equals one modulo `m`. If `a,m` are
coprime the unique candidate is exactly `ZMod`'s inverse value, including `m=1`.
Each candidate and the retained result have only the modulus's binary size.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularInverseBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

def search (a m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => if a * k % m = 1 % m then k else search a m k

theorem search_le (a m k : ℕ) : search a m k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [search]; split_ifs <;> omega

theorem search_eq_inverse (a m : ℕ) (hm : 0 < m) (hco : a.Coprime m) :
    search a m m = ((a : ZMod m)⁻¹).val := by
  have : NeZero m := ⟨hm.ne'⟩
  let b := ((a : ZMod m)⁻¹).val
  have hb : b < m := ZMod.val_lt _
  have hcast : ((a * b : ℕ) : ZMod m) = (1 : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_one] using ZMod.mul_val_inv hco
  have htest : a * b % m = 1 % m := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
  have hunique (k : ℕ) (hk : k < m) : a * k % m = 1 % m ↔ k = b := by
    constructor
    · intro ht
      have hmul : a * k ≡ a * b [MOD m] := ht.trans htest.symm
      have he := Nat.ModEq.cancel_left_of_coprime hco.symm hmul
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hb] using he
    · rintro rfl
      exact htest
  have hprefix (k : ℕ) (hk : k ≤ m) : search a m k = if b < k then b else 0 := by
    induction k with
    | zero => simp [search]
    | succ k ih =>
      rw [search]
      by_cases he : k = b
      · rw [ite_eq_left ((hunique k (by omega)).mpr he), ite_eq_left (by omega : b < k + 1)]
        exact he
      · rw [ite_eq_right (by intro ht; exact he ((hunique k (by omega)).mp ht)), ih (by omega)]
        by_cases hbk : b < k
        · rw [ite_eq_left hbk, ite_eq_left (by omega : b < k + 1)]
        · rw [ite_eq_right hbk, ite_eq_right (by omega : ¬ b < k + 1)]
  rw [hprefix m le_rfl, ite_eq_left hb]

def modulus (c : List Bool) : List Bool := BinaryNat.succ (pairSnd c)
def tested (p : List Bool) : List Bool := BinaryNat.mulMod
  (pair (modulus (pairFst p)) (pair (pairFst (pairFst p)) (BoundedFold.counter p)))
def oneResidue (p : List Bool) : List Bool := BinaryNat.mod (pair [true] (modulus (pairFst p)))
def successful (p : List Bool) : Prop := Nat.fromBitsLE (tested p) = Nat.fromBitsLE (oneResidue p)
instance (p : List Bool) : Decidable (successful p) := inferInstanceAs (Decidable (_ = _))
def update (p : List Bool) : List Bool :=
  if successful p then BinaryNat.normalize (BoundedFold.counter p) else BinaryNat.normalize (BoundedFold.accumulator p)
def value (c : List Bool) : List Bool :=
  let m := Nat.fromBitsLE (pairSnd c) + 1
  (search (Nat.fromBitsLE (pairFst c)) m m).bits

theorem modulus_mem_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

theorem tested_mem_FP : tested ∈ FP := by
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have ha := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair ha BoundedFold.counter_mem_FP)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := tested) h ?_
  intro p
  simp only [Function.comp_apply, tested]

theorem oneResidue_mem_FP : oneResidue ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (constFn_mem_FP [true]) (mem_FP_comp pairFst_mem_FP modulus_mem_FP)) BinaryNat.mod_mem_FP
  refine mem_FP_of_eq (g := oneResidue) h ?_
  intro p
  simp only [Function.comp_apply, oneResidue]

theorem successful_fppred : FPPred successful := by
  refine ((BinaryNat.le_fppred tested_mem_FP oneResidue_mem_FP).and
    (BinaryNat.le_fppred oneResidue_mem_FP tested_mem_FP)).of_iff ?_
  intro p
  dsimp only [successful]
  omega

theorem update_mem_FP : update ∈ FP :=
  successful_fppred.ite_mem_FP (mem_FP_comp BoundedFold.counter_mem_FP BinaryNat.normalize_mem_FP)
    (mem_FP_comp BoundedFold.accumulator_mem_FP BinaryNat.normalize_mem_FP)

theorem update_packet (c : List Bool) (k v : ℕ) : update (BoundedFold.packet c k v.bits) =
    (if Nat.fromBitsLE (pairFst c) * k % (Nat.fromBitsLE (pairSnd c) + 1) =
      1 % (Nat.fromBitsLE (pairSnd c) + 1) then k else v).bits := by
  simp only [update, successful, tested, oneResidue, BoundedFold.context_packet, BoundedFold.counter_packet,
    BoundedFold.accumulator_packet, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    modulus, BinaryNat.mulMod_pair, BinaryNat.mod_pair, BinaryNat.succ_eq_bits,
    show Nat.fromBitsLE [true] = 1 from rfl]
  split_ifs <;> rfl

theorem fold_eq (c : List Bool) (k : ℕ) : BoundedFold.fold update (fun _ => []) c k =
    (search (Nat.fromBitsLE (pairFst c)) (Nat.fromBitsLE (pairSnd c) + 1) k).bits := by
  induction k with
  | zero => rfl
  | succ k ih => rw [BoundedFold.fold, ih, update_packet, search]

noncomputable def evaluator : SpaceFunction value := by
  have hs : ∀ c k, k ≤ Nat.fromBitsLE (modulus c) →
      (BoundedFold.fold update (fun _ => []) c k).length ≤ (Polynomial.X + 1 : Polynomial ℕ).eval c.length := by
    intro c k hk
    rw [fold_eq, Nat.size_eq_bits_len]
    have hk' : k ≤ Nat.fromBitsLE (pairSnd c) + 1 := by
      simpa only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits] using hk
    have hraw := (Nat.fromBitsLE_lt_pow_length (pairSnd c)).trans_le
      (Nat.pow_le_pow_right (by decide) (pairSnd_length_le c))
    have hp : Nat.fromBitsLE (pairSnd c) + 1 < 2 ^ (c.length + 1) := by
      rw [pow_succ]
      have := pow_pos (by decide : 0 < (2 : ℕ)) c.length
      omega
    have h := Nat.size_le.mpr (((search_le (Nat.fromBitsLE (pairFst c)) (Nat.fromBitsLE (pairSnd c) + 1) k).trans hk').trans_lt hp)
    simpa only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] using h
  let E := BoundedFold.evaluator (SpaceFunction.ofFP update update_mem_FP) modulus (fun _ => [])
    modulus_mem_FP (constFn_mem_FP []) (Polynomial.X + 1) hs
  refine E.congr (funext fun c => ?_)
  simp only [modulus, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, fold_eq, value]

theorem value_pair (a m : ℕ) (hm : 0 < m) (hco : a.Coprime m) :
    value (pair (BinaryNatCode.encode a) (BinaryNatCode.encode (m - 1))) =
      BinaryNatCode.encode (((a : ZMod m)⁻¹).val) := by
  simp only [value, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.sub_add_cancel (by omega : 1 ≤ m), search_eq_inverse a m hm hco]

end LeanCanny.Algebra.ModularInverseBits
