/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerSignSpace
public import LeanCanny.Algebra.ChineseRemainderRankSpace

/-!
# Integer CRT rank bits from certified residue access

The same indexed moduli and dyadic precision used for sign recovery give
certified access to any selected correction-rank bit. This supplies a component
of integer digit recovery; the remaining large product/sum digit arithmetic
is not included in this certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.IntegerRankBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Algebra.ChineseRemainder

def system (budget : List Bool → List Bool) (c : List Bool) :=
  indexedSystem (Nat.fromBitsLE (IntegerSignBits.bound budget c))

noncomputable def rank (budget : List Bool → List Bool) (z : List Bool → ℤ) (c : List Bool) : ℕ :=
  (system budget c).integerSum (fun i => (z c : ZMod ((system budget c).modulus i)).val) / (system budget c).product

theorem evaluator {rho : List Bool → List Bool} (R : SpaceFunction rho)
    (budget index : List Bool → List Bool) (hb : budget ∈ FP) (hi : index ∈ FP) (z : List Bool → ℤ)
    (hres : ∀ c (m : ℕ), 0 < m →
      rho (pair c (BinaryNatCode.encode (m - 1))) = BinaryNatCode.encode ((z c : ZMod m).val)) :
    SpaceFunction (fun c => if (rank budget z c).testBit (Nat.fromBitsLE (index c)) then [true] else []) := by
  let N := fun c => Nat.fromBitsLE (IntegerSignBits.bound budget c)
  let F := fun c => indexedSystem (N c)
  let r := fun c (i : Fin (N c + 1)) => (z c : ZMod ((F c).modulus i)).val
  have hN (c : List Bool) : N c = 2 * Nat.fromBitsLE (budget c) + 6 := by
    simp only [N, IntegerSignBits.bound_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hcount (c : List Bool) : Nat.fromBitsLE (IntegerSignBits.count budget c) = N c + 1 := by
    simp only [IntegerSignBits.count, Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, N]
  have hp (c : List Bool) : Nat.fromBitsLE (IntegerSignBits.precision budget c) = precisionBits (N c) := by
    simp only [IntegerSignBits.precision_code, BinaryNatCode.encode, Nat.fromBitsLE_bits, hN]
  let P := PreparationBits.evaluator R (IntegerSignBits.bound budget) (IntegerSignBits.bound_mem_FP hb)
  change SpaceFunction (fun c => if ((F c).integerSum (r c) / (F c).product).testBit
    (Nat.fromBitsLE (index c)) then [true] else [])
  refine rankBitEvaluatorOfCount P (IntegerSignBits.count budget) (IntegerSignBits.precision budget) index
    (IntegerSignBits.count_mem_FP hb) (IntegerSignBits.precision_mem_FP hb) hi
    (fun c => N c + 1) hcount F r ?_ ?_
  · intro c
    rw [hp]
    have he := indexed_precision_sufficient (N c)
    have he' : 2 * (N c + 1) * (F c).product < 2 ^ precisionBits (N c) := by
      simpa only [F, Fintype.card_fin] using he
    nlinarith [he']
  · intro c i
    exact PreparationBits.value_pair (IntegerSignBits.bound budget) rho c (z c) (hres c) i

theorem rank_le (budget : List Bool → List Bool) (z : List Bool → ℤ) (c : List Bool) :
    rank budget z c ≤ Nat.fromBitsLE (IntegerSignBits.count budget c) := by
  let F := system budget c
  let r := fun i => (z c : ZMod (F.modulus i)).val
  have hp : Fintype.card (Fin (Nat.fromBitsLE (IntegerSignBits.bound budget c) + 1)) * F.product <
      2 ^ Nat.fromBitsLE (IntegerSignBits.precision budget c) := by
    have he := indexed_precision_sufficient (Nat.fromBitsLE (IntegerSignBits.bound budget c))
    have hprec : Nat.fromBitsLE (IntegerSignBits.precision budget c) =
        precisionBits (Nat.fromBitsLE (IntegerSignBits.bound budget c)) := by
      simp only [IntegerSignBits.precision_code, IntegerSignBits.bound_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rw [hprec]
    have he' : 2 * (Nat.fromBitsLE (IntegerSignBits.bound budget c) + 1) * F.product <
        2 ^ precisionBits (Nat.fromBitsLE (IntegerSignBits.bound budget c)) := by
      simpa only [F, system, Fintype.card_fin] using he
    simp only [Fintype.card_fin]
    nlinarith [he']
  have he := F.truncatedRank_le r (2 ^ Nat.fromBitsLE (IntegerSignBits.precision budget c)) (by positivity)
  rw [F.truncatedRank_eq r _ (by positivity) hp] at he
  simpa only [rank, F, r, system, Fintype.card_fin, IntegerSignBits.count, Function.comp_apply,
    BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits] using he

theorem rank_bits_le (budget : List Bool → List Bool) (z : List Bool → ℤ) (c : List Bool) :
    (rank budget z c).size ≤ (IntegerSignBits.count budget c).length :=
  Nat.size_le.mpr ((rank_le budget z c).trans_lt (Nat.fromBitsLE_lt_pow_length _))

theorem reconstruct (budget : List Bool → List Bool) (z : List Bool → ℤ)
    (hbudget : ∀ c, (z c).natAbs.size ≤ Nat.fromBitsLE (budget c)) (c : List Bool) :
    let F := system budget c
    let x := F.integerSum (fun i => (z c : ZMod (F.modulus i)).val) - rank budget z c * F.product
    (if x ≤ F.product / 2 then (x : ℤ) else (x : ℤ) - F.product) = z c := by
  let F := system budget c
  let r := fun i => (z c : ZMod (F.modulus i)).val
  let D := 2 ^ Nat.fromBitsLE (IntegerSignBits.precision budget c)
  have hr (i) : (r i : ZMod (F.modulus i)) = z c := by
    let : NeZero (F.modulus i) := ⟨(F.positive i).ne'⟩
    exact ZMod.natCast_zmod_val _
  have hprec : Nat.fromBitsLE (IntegerSignBits.precision budget c) =
      precisionBits (Nat.fromBitsLE (IntegerSignBits.bound budget c)) := by
    simp only [IntegerSignBits.precision_code, IntegerSignBits.bound_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hp : Fintype.card (Fin (Nat.fromBitsLE (IntegerSignBits.bound budget c) + 1)) * F.product < D := by
    have he := indexed_precision_sufficient (Nat.fromBitsLE (IntegerSignBits.bound budget c))
    have he' : 2 * (Nat.fromBitsLE (IntegerSignBits.bound budget c) + 1) * F.product < D := by
      simpa only [D, hprec, F, system, Fintype.card_fin] using he
    simp only [Fintype.card_fin]
    nlinarith [he']
  have hmag : 2 * (z c).natAbs < F.product := by
    have hn : Nat.fromBitsLE (IntegerSignBits.bound budget c) = 2 * Nat.fromBitsLE (budget c) + 6 := by
      simp only [IntegerSignBits.bound_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have he := IntegerModular.two_natAbs_lt_lcmUpto (z c) (Nat.fromBitsLE (budget c)) (hbudget c)
    simpa only [F, system, indexedSystem_product, hn] using he
  have he := F.centered_reconstruction r (z c) hr hmag D (by dsimp [D]; positivity) hp
  dsimp only at he ⊢
  rw [F.truncatedRank_eq r D (by dsimp [D]; positivity) hp] at he
  exact he

end LeanCanny.Algebra.IntegerRankBits
